:- module day17.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, float, math, pair, maybe, exception.
:- import_module utils.

:- type area ---> area(min_x :: int, max_x :: int, min_y :: int, max_y :: int).

:- func probe_highest_y(area) = int.
probe_highest_y(Area) = arith_series_sum(1, VY_0, VY_0) :-
  VY_0 = max_vy(Area).

:- func min_vx(area) = int is semidet.
min_vx(Area) = MinVX :-
  % calculate roots of sum[0..MinVX] = Area^min_x
  Roots = solve_quadratic(1.0, 1.0, -2.0 * float(Area^min_x)),
  (if Roots = one_root(SingleRoot) then
    MinVX = ceiling_to_int(SingleRoot)
  else if Roots = two_roots(Root1, Root2) then
    MaxRoot = max(Root1, Root2), % only want the positive root
    MinVX = ceiling_to_int(MaxRoot)
  else
    fail
  ).

:- func max_vx(area) = int.
max_vx(Area) = Area^max_x.  % can't be greater than that, otherwise we miss the area entirely

:- func min_vy(area) = int.
min_vy(Area) = Area^min_y.

:- func max_vy(area) = int.
max_vy(Area) = abs(Area^min_y) - 1.

:- func min_t_within_x_bounds(int, area) = int is semidet.
min_t_within_x_bounds(VX_0, Area) = MinT :-
  % calculate roots of x(V_0, t) = Area^min_x
  Roots = solve_quadratic(-0.5, float(VX_0) + 0.5, -float(Area^min_x)),
  (if Roots = one_root(SingleRoot) then
    MinT = ceiling_to_int(SingleRoot)
  else if Roots = two_roots(Root1, Root2) then
    % only want the max within bounds
    MinRoot = ceiling_to_int(min(Root1, Root2)),
    (if x(VX_0, MinRoot) >= Area^min_x then
      MinT = MinRoot
    else
      MinT = ceiling_to_int(min(Root1, Root2))
    )
  else
    fail
  ).

:- func max_t_within_x_bounds(int, area) = int is semidet.
max_t_within_x_bounds(VX_0, Area) = MaxT :-
  % calculate roots of x(V_0, t) = Area^max_x
  Roots = solve_quadratic(-0.5, float(VX_0) + 0.5, -float(Area^max_x)),
  (if Roots = one_root(SingleRoot) then
    MaxT = floor_to_int(SingleRoot)
  else if Roots = two_roots(Root1, Root2) then
    % only want the max within bounds
    MaxRoot = floor_to_int(max(Root1, Root2)),
    (if x(VX_0, MaxRoot) =< Area^max_x then
      MaxT = MaxRoot
    else
      MaxT = floor_to_int(min(Root1, Root2))
    )
  else
    fail
  ).

:- func max_t_within_y_bounds(int, area) = int is semidet.
max_t_within_y_bounds(VY_0, Area) = MaxT :-
  % - time from (0, 0) to highest Y: VY_0
  % - time from highest Y back to (0, 0): VY_0
  FirstHalfT = (if VY_0 > 0 then 2 * VY_0 else 0),

  % - time from (0, 0) until Area^max_y: roots of y(VY_0, t) = Area^min_y
  Roots = solve_quadratic(-0.5, float(VY_0) + 0.5, -float(Area^min_y)),
  (if Roots = one_root(SingleRoot) then
    SecondHalfT = floor_to_int(SingleRoot)
  else if Roots = two_roots(Root1, Root2) then
    % only want the max within bounds
    MaxRoot = floor_to_int(max(Root1, Root2)),
    (if y(VY_0, MaxRoot) >= Area^min_y then
      SecondHalfT = MaxRoot
    else
      SecondHalfT = floor_to_int(min(Root1, Root2))
    )
  else
    fail
  ),
  MaxT = FirstHalfT + SecondHalfT.

:- func max_t_within_bounds(int, int, area) = int is det.
max_t_within_bounds(VX, VY, Area) = max(MaxTFromX, MaxTFromY) :-
  MaxTFromX = (if max_t_within_x_bounds(VX, Area) = MTX then MTX else 1),
  MaxTFromY = (if max_t_within_y_bounds(VY, Area) = MTY then MTY else 1).

:- func x(int, int) = int.
x(VX_0, T) = X :-
  (if T =< VX_0 then
    X = (T * (2 * VX_0 + 1) - T * T) / 2
  else
    X = arith_series_sum(1, VX_0, VX_0)
  ).

:- func y(int, int) = int.
y(VY_0, T) = (T * (2 * VY_0 + 1) - T * T) / 2.

:- pred find_distinct_velocities(area::in, list(pair(int, int))::out) is semidet.
find_distinct_velocities(Area, AllVelocities) :-
  filter_map(
    % for each VX
    (pred(VX::in, Velocities::out) is semidet :- filter_map(
      % for each VY
      (pred(VY::in, Pair::out) is semidet :-
        % simulate Ts until one is within bounds or it went beyond bounds
        foldl_while(
          (pred(T::in, MaybeTIn::in, MaybeTOut::out) is semidet :-
            X = x(VX, T),
            Y = y(VY, T),
            (if (X > Area^max_x ; Y < Area^min_y) then
              % beyond bounds
              fail
            else if MaybeTIn = yes(_) then
              % already found
              fail
            else if X >= Area^min_x, Y =< Area^max_y then
              % within bounds, keep it
              MaybeTOut = yes(T)
            else
              % keep going
              MaybeTOut = no
            )
          ),
          min_t_within_x_bounds(VX, Area) .. max_t_within_bounds(VX, VY, Area),
          no,
          MaybeT
        ),
        % if there's at least one T within the area, keep this (VX, VY)
        MaybeT = yes(_),
        Pair = pair(VX, VY)
      ),
      min_vy(Area) .. max_vy(Area),
      Velocities
    )),
    min_vx(Area) .. max_vx(Area),
    VelocitiesByVX
  ),
  AllVelocities = condense(VelocitiesByVX).

:- pred solve(area::in, io::di, io::uo) is det.
solve(Area, !IO) :-
  io.print_line("Solving for " ++ string(Area) ++ ":", !IO),

  % Part 1
  ProbeHighestY = probe_highest_y(Area),
  io.print_line("Part 1: " ++ string(ProbeHighestY), !IO),

  % Part 2
  (if find_distinct_velocities(Area, AllVelocities) then
    io.format("Part 2: %i\r\n", [i(length(AllVelocities))], !IO)
  else
    true
  ),

  io.nl(!IO).

main(!IO) :-
  Inputs = [
    area(20, 30, -10, -5),
    area(175, 227, -134, -79)
  ],
  foldl(solve, Inputs, !IO).