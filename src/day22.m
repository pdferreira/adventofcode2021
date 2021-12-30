:- module day22.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, char, set, bool, solutions.
:- import_module utils.

:- type position ---> position(x :: int, y :: int, z :: int).
:- type cuboid ---> cuboid(min_x :: int, max_x :: int, min_y :: int, max_y :: int, min_z :: int, max_z :: int).
:- type reboot_step ---> step(enable :: bool, area :: cuboid).

:- pred parse_coord_range(string::in, int::out, int::out) is semidet.
parse_coord_range(CoordRange, Min, Max) :-
  [_, Range] = split_at_char('=', CoordRange),
  [MinStr, MaxStr] = split_at_string("..", Range),
  string.to_int(MinStr, Min),
  string.to_int(MaxStr, Max).

:- func parse_cuboid(string) = cuboid is semidet.
parse_cuboid(CuboidStr) = cuboid(MinX, MaxX, MinY, MaxY, MinZ, MaxZ) :-
  [XRange, YRange, ZRange] = split_at_char(',', CuboidStr),
  parse_coord_range(XRange, MinX, MaxX),
  parse_coord_range(YRange, MinY, MaxY),
  parse_coord_range(ZRange, MinZ, MaxZ).

:- func parse_reboot_step(string) = reboot_step is semidet.
parse_reboot_step(Line) = step(Enable, Area) :-
  [EnableStr, CuboidStr] = split_at_char(' ', Line),
  Enable = (if EnableStr = "on" then yes else no),
  Area = parse_cuboid(CuboidStr).

:- func get_all_points(cuboid) = set(position).
get_all_points(Cuboid) = solutions_set(position_in_cuboid(Cuboid)).

:- pred position_in_cuboid(cuboid::in, position::out) is nondet.
position_in_cuboid(Cuboid, position(X, Y, Z)) :-
  member(X, Cuboid^min_x .. Cuboid^max_x),
  member(Y, Cuboid^min_y .. Cuboid^max_y),
  member(Z, Cuboid^min_z .. Cuboid^max_z).

:- func run_reboot_step(reboot_step, set(position)) = set(position).
run_reboot_step(step(yes, Cuboid), EnabledPoints) = UP :-
  UP = union(EnabledPoints, get_all_points(Cuboid)),
  trace [io(!IO)] io.format("[%i] After union\r\n", [i(count(UP))], !IO).
run_reboot_step(step(no, Cuboid), EnabledPoints) = DP :-
  DP = difference(EnabledPoints, get_all_points(Cuboid)),
  trace [io(!IO)] io.format("[%i] After difference\r\n", [i(count(DP))], !IO).

:- func reboot(list(reboot_step)) = set(position).
reboot(Steps) = foldl(run_reboot_step, Steps, set.init).

:- func initialize(list(reboot_step)) = set(position).
initialize(Steps) = reboot(filter(is_initialization_step, Steps)).

:- pred is_initialization_step(reboot_step::in) is semidet.
is_initialization_step(step(_, Cuboid)) :-
  Cuboid^min_x >= -50, Cuboid^max_x =< 50,
  Cuboid^min_y >= -50, Cuboid^max_y =< 50,
  Cuboid^min_z >= -50, Cuboid^max_z =< 50.

:- func volume(cuboid) = int.
volume(cuboid(MinX, MaxX, MinY, MaxY, MinZ, MaxZ)) = (MaxX - MinX + 1) * (MaxY - MinY + 1) * (MaxZ - MinZ + 1).

:- func total_volume(set(cuboid)) = int.
total_volume(CuboidSet) = sum(map(volume, to_sorted_list(CuboidSet))).

:- pred cuboid_contains(cuboid::in, cuboid::in) is semidet.
cuboid_contains(C1, C2) :-
  C1^min_x =< C2^min_x, C2^max_x =< C1^max_x,
  C1^min_y =< C2^min_y, C2^max_y =< C1^max_y,
  C1^min_z =< C2^min_z, C2^max_z =< C1^max_z.

:- pred is_valid_cuboid(cuboid::in) is semidet.
is_valid_cuboid(cuboid(MinX, MaxX, MinY, MaxY, MinZ, MaxZ)) :- 
  MinX =< MaxX,
  MinY =< MaxY,
  MinZ =< MaxZ.

:- func cuboid_intersect(cuboid, cuboid) = cuboid is semidet.
cuboid_intersect(C1, C2) = CIntersection :- 
  MinX: int = max(C1^min_x, C2^min_x),
  MaxX: int = min(C1^max_x, C2^max_x),
  MinY: int = max(C1^min_y, C2^min_y),
  MaxY: int = min(C1^max_y, C2^max_y),
  MinZ: int = max(C1^min_z, C2^min_z),
  MaxZ: int = min(C1^max_z, C2^max_z),
  CIntersection = cuboid(MinX, MaxX, MinY, MaxY, MinZ, MaxZ),
  is_valid_cuboid(CIntersection).

% Not sure if this changes anything, but the implementation assumes C2 is 100% contained in C1
% Invariant: output set has cuboids with no intersections
:- func cuboid_difference(cuboid, cuboid) = set(cuboid).
cuboid_difference(C1, C2) = list_to_set(filter(is_valid_cuboid, ResultingCuboids))  :-
  % Generically assume C2 is in the middle of C1
  % and generate the slicing of the surroundings in 6 non-overlapping cuboids
  ResultingCuboids = [
    % Back face (min, min, min) - (max, max, C2.min - 1)
    cuboid(C1^min_x, C1^max_x, C1^min_y, C1^max_y, C1^min_z, C2^min_z - 1),
    % Front face (min, min, C2.max + 1) - (max, max, max)
    cuboid(C1^min_x, C1^max_x, C1^min_y, C1^max_y, C2^max_z + 1, C1^max_z),
    % Left middle cut (min, min, C2.min) - (C2.min - 1, max, C2.max)
    cuboid(C1^min_x, C2^min_x - 1, C1^min_y, C1^max_y, C2^min_z, C2^max_z),
    % Right middle cut (C2.max + 1, min, C2.min) - (max, max, C2.max)
    cuboid(C2^max_x + 1, C1^max_x, C1^min_y, C1^max_y, C2^min_z, C2^max_z),
    % Middle top cube (C2.min, C2.max + 1, C2.min) - (C2.max, max, C2.max)
    cuboid(C2^min_x, C2^max_x, C2^max_y + 1, C1^max_y, C2^min_z, C2^max_z),
    % Middle buttom cube (C2.min, min, C2.min) - (C2.max, C2.min - 1, C2.max)
    cuboid(C2^min_x, C2^max_x, C1^min_y, C2^min_y - 1, C2^min_z, C2^max_z)
  ].

% Invariant: input and output sets have cuboids with no intersections
:- func cuboid_insert(cuboid, set(cuboid)) = set(cuboid).
cuboid_insert(NewC, Cs) = CInsert :-
  (if any_true(pred(C::in) is semidet :- cuboid_contains(C, NewC), Cs) then
    CInsert = Cs
  else if filter(cuboid_contains(NewC), Cs, Contained, NotContained), is_non_empty(Contained) then
    CInsert = cuboid_insert(NewC, NotContained)
  else if remove_least(SomeC, Cs, RemainingCs) then
    (if cuboid_intersect(SomeC, NewC) = C3 then 
      NewCs = cuboid_difference(NewC, C3),
      CInsert = set.insert(foldl(cuboid_insert, NewCs, RemainingCs), SomeC)
    else
      CInsert = set.insert(cuboid_insert(NewC, RemainingCs), SomeC)
    )
  else
    CInsert = list_to_set([NewC])
  ).

:- func run_reboot_step_v2(reboot_step, set(cuboid)) = set(cuboid).
run_reboot_step_v2(step(yes, Area), EnabledCuboids) = CI :- 
  CI = cuboid_insert(Area, EnabledCuboids),
  trace [io(!IO)] io.format("[%i] After union\r\n", [i(total_volume(CI))], !IO).

run_reboot_step_v2(step(no, Area), EnabledCuboids) = CD :-
  CD = set.power_union(map(
    (func(C) = CDiff :-
      (if cuboid_intersect(C, Area) = CInter then
        CDiff = cuboid_difference(C, CInter)
      else
        CDiff = list_to_set([C])
      )
    ),
    EnabledCuboids)
  ),
  trace [io(!IO)] io.format("[%i] After difference\r\n", [i(total_volume(CD))], !IO).

:- func reboot_v2(list(reboot_step)) = set(cuboid).
reboot_v2(Steps) = foldl(run_reboot_step_v2, Steps, set.init).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    map(to_pred(parse_reboot_step), Lines, RebootSteps)
  then
    % Part 1
    EnabledPointsAfterInit = initialize(RebootSteps),
    io.format("Part 1: %i\r\n", [i(count(EnabledPointsAfterInit))], !IO),

    % Part 2
    EnabledCuboidsAfterReboot = reboot_v2(RebootSteps),
    NumEnabledPointsAfterReboot = total_volume(EnabledCuboidsAfterReboot),
    io.format("Part 2: %i\r\n", [i(NumEnabledPointsAfterReboot)], !IO)
  else
    true
  ),
  io.nl(!IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "example1",
    "example2",
    "example3",
    "input"
  ]),
  foldl(solve, Inputs, !IO).