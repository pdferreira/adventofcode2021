:- module day11.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, array2d, pair, char, solutions.
:- import_module utils.

:- type energy_level == int.
:- type octopi_grid == array2d(energy_level).

:- pred parse_octopi_grid(list(string)::in, octopi_grid::array2d_uo) is det.
parse_octopi_grid(Lines, Grid) :-
  EnergiesLL = map(
    pipe2(
      to_char_list,
      map(det_decimal_digit_to_int)
    ),
    Lines
  ): list(list(energy_level)),
  Grid = array2d.from_lists(EnergiesLL).

:- pred adjacent_position(int::in, int::in, int::in, int::in, pair(int, int)::out) is nondet.
adjacent_position(MaxCol, MaxRow, Row, Col, AdjPosition) :-
  (
    Col + 1 < MaxCol, Row + 1 < MaxRow, AdjPosition = pair(Row + 1, Col + 1)
  ;
    Col + 1 < MaxCol, AdjPosition = pair(Row, Col + 1)
  ;
    Row + 1 < MaxRow, AdjPosition = pair(Row + 1, Col)
  ;
    Col > 0, AdjPosition = pair(Row, Col - 1)
  ;
    Row > 0, AdjPosition = pair(Row - 1, Col)
  ;
    Col > 0, Row + 1 < MaxRow, AdjPosition = pair(Row + 1, Col - 1)
  ;
    Col > 0, Row > 0, AdjPosition = pair(Row - 1, Col - 1)
  ;
    Col + 1 < MaxCol, Row > 0, AdjPosition = pair(Row - 1, Col + 1)
  ).

:- pred simulate_flashes(int::in, int::in, octopi_grid::array2d_di, octopi_grid::array2d_uo, int::out) is det.
simulate_flashes(Row, Col, !Grid, OutNumFlashes) :-
  bounds(!.Grid, MaxRow, MaxCol),
  EnergyLevel = !.Grid^elem(Row, Col),
  AlreadyFlashedLevel = (MaxRow * MaxCol) + 1,  % use a big level as a marker for already flashed
  (if EnergyLevel > 9, EnergyLevel < AlreadyFlashedLevel then
    Flash = 1,
    % Mark as flashed
    set(Row, Col, AlreadyFlashedLevel, !Grid),
    % Increase by 1 all the adjacent
    solutions(adjacent_position(MaxRow, MaxCol, Row, Col), Positions),
    foldl(
      (pred(Pos::in, GridIn::in, GridOut::out) is det :-
        R = fst(Pos),
        C = snd(Pos),
        E = GridIn^elem(R, C),
        set(R, C, E + 1, GridIn, GridOut)
      ),
      Positions,
      !Grid
    )
  else
    Flash = 0
  ),
  (if Col + 1 < MaxCol then
    simulate_flashes(Row, Col + 1, !Grid, NumFlashes),
    OutNumFlashes = Flash + NumFlashes
  else if Row + 1 < MaxRow then
    simulate_flashes(Row + 1, 0, !Grid, NumFlashes),
    OutNumFlashes = Flash + NumFlashes
  else
    OutNumFlashes = Flash
  ).

:- pred simulate_flashes(octopi_grid::array2d_di, octopi_grid::array2d_uo, int::out) is det.
simulate_flashes(!Grid, OutNumFlashes) :-
  simulate_flashes(0, 0, !Grid, NumFlashes),
  (if NumFlashes > 0 then
    simulate_flashes(!Grid, NextNumFlashes),
    OutNumFlashes = NumFlashes + NextNumFlashes
  else
    OutNumFlashes = NumFlashes
  ).

:- pred simulate_step(octopi_grid::array2d_di, octopi_grid::array2d_uo, int::out) is det.
simulate_step(!Grid, FlashCount) :-
  % Increase all energies by 1
  update2d((pred(E::in, NewE::out) is semidet :- NewE = E + 1), !Grid),
  % Trigger all flashes
  simulate_flashes(!Grid, FlashCount),
  % Reset energies of all > 9
  update2d((pred(E::in, NewE::out) is semidet :- E > 9, NewE = 0), !Grid).

:- pred simulate(octopi_grid::array2d_di, octopi_grid::array2d_uo, int::in, int::out) is det.
simulate(!Grid, N, FlashCount) :-
  (if N = 0 then
    FlashCount = 0
  else
    simulate_step(!Grid, StepFlashCount),
    simulate(!Grid, N - 1, NextFlashCount),
    FlashCount = StepFlashCount + NextFlashCount
  ).

:- pred simulate_until_all_flashes(octopi_grid::array2d_di, octopi_grid::array2d_uo, int::in, int::out) is det.
simulate_until_all_flashes(!Grid, !StepN) :-
  !:StepN = !.StepN + 1,
  simulate_step(!Grid, StepFlashCount),
  
  bounds(!.Grid, MaxRow, MaxCol),
  (if StepFlashCount = MaxRow * MaxCol then
    true
  else
    simulate_until_all_flashes(!Grid, !StepN)
  ).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  parse_octopi_grid(Lines, Grid),

  % Part 1
  copy(Grid, Part1Grid), 
  simulate(Part1Grid, _, 100, OutNumFlashes),
  io.print_line("Part 1: " ++ string(OutNumFlashes), !IO),

  % Part 2
  copy(Grid, Part2Grid),
  simulate_until_all_flashes(Part2Grid, _, 0, StepWhenAllFlashes),
  io.print_line("Part 2: " ++ string(StepWhenAllFlashes), !IO),

  io.nl(!IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "example1",
    "example2",
    "part1"
  ]),
  foldl(solve, Inputs, !IO).