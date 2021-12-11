:- module day07.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, float, solutions.
:- import_module utils.

:- type fuel == int.
:- type position == int.
:- type crabs == list(position).

:- pred read_crabs(string::in, crabs::out) is semidet.
read_crabs(Line, CrabList) :-
  PositionsStr = split_at_string(",", Line),
  map(to_int, PositionsStr, CrabList).

:- func fuel_spent_p1(crabs, position) = fuel.
fuel_spent_p1(CrabList, AlignPos) = sum(FuelSpentList) :-
  FuelSpentList = map(func(Pos) = abs(Pos - AlignPos), CrabList).

:- func fuel_spent_p2(crabs, position) = fuel.
fuel_spent_p2(CrabList, AlignPos) = sum(FuelSpentList) :-
  FuelSpentList = map(
    (func(Pos) = FuelSpent :- 
      NumSteps = abs(Pos - AlignPos),
      FuelSpent = arith_series_sum(1, NumSteps, NumSteps)
    ), 
    CrabList).

:- func find_min_fuel_spent(crabs, func(crabs, position) = fuel) = fuel is semidet.
find_min_fuel_spent(CrabList, CalcFuelSpent) = min(FuelSpentList) :-
  MinPos = min(CrabList),
  MaxPos = max(CrabList),
  solutions(nondet_int_in_range(MinPos, MaxPos), PosList),
  FuelSpentList = map(curry(CalcFuelSpent)(CrabList), PosList).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    [L] = Lines,
    read_crabs(L, CrabList)
  then
    % Part 1
    (if 
      MinFuelSpent = find_min_fuel_spent(CrabList, fuel_spent_p1)
    then
      io.print_line("Part 1: " ++ string(MinFuelSpent), !IO)
    else
      true
    ),

    % Part 2
    (if
      MinFuelSpentP2 = find_min_fuel_spent(CrabList, fuel_spent_p2) 
    then
      io.print_line("Part 2: " ++ string(MinFuelSpentP2), !IO)
    else
      true
    )
  else
    true
  ).

main(!IO) :-
  solve("inputs/" ++ $module ++ "_example", !IO),
  io.nl(!IO),
  solve("inputs/" ++ $module ++ "_part1", !IO).
