:- module day25.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, char, array2d, pair, bool, exception.
:- import_module utils.

:- type sea_floor == array2d(char).
:- mode sf_di == array2d_di.
:- mode sf_uo == array2d_uo.
:- type position == pair(int, int).

:- pred parse_sea_floor(list(string)::in, sea_floor::sf_uo) is det.
parse_sea_floor(Lines, Matrix) :-
  Matrix = array2d.from_lists(map(to_char_list, Lines)).

:- pred herd_step_aux(char::in, (func(position) = position)::in, position::in, sea_floor::in, sea_floor::sf_di, sea_floor::sf_uo, bool::in, bool::out) is det.
herd_step_aux(HerdType, MoveFn, (CurrRow - CurrCol), PrevSeaFloor, !SeaFloor, !Changed) :-
  bounds(PrevSeaFloor, MaxRow, MaxCol),
  CurrTile = PrevSeaFloor^elem(CurrRow, CurrCol),
  (if 
    CurrTile = HerdType,
    MoveFn(pair(CurrRow, CurrCol)) = (NextRow - NextCol),
    RealNextRow = NextRow mod MaxRow,
    RealNextCol = NextCol mod MaxCol,
    ('.' = PrevSeaFloor^elem(RealNextRow, RealNextCol))
  then
    set(CurrRow, CurrCol, '.', !SeaFloor),
    set(RealNextRow, RealNextCol, HerdType, !SeaFloor),
    !:Changed = yes
  else
    true
  ),
  (if CurrCol + 1 < MaxCol then
    herd_step_aux(HerdType, MoveFn, pair(CurrRow, CurrCol + 1), PrevSeaFloor, !SeaFloor, !Changed)
  else if CurrRow + 1 < MaxRow then
    herd_step_aux(HerdType, MoveFn, pair(CurrRow + 1, 0), PrevSeaFloor, !SeaFloor, !Changed)
  else
    true
  ).

:- pred herd_step(char::in, (func(position) = position)::in, sea_floor::sf_di, sea_floor::sf_uo, bool::out) is det.
herd_step(HerdType, MoveFn, !SeaFloor, Changed) :-
  copy(!.SeaFloor, PrevSeaFloor),
  herd_step_aux(HerdType, MoveFn, pair(0, 0), PrevSeaFloor, !SeaFloor, no, Changed).

:- pred simulate_until_herd_stops(sea_floor::sf_di, sea_floor::sf_uo, int::in, int::out) is det.
simulate_until_herd_stops(!SeaFloor, !NumSteps) :-
  % trace [io(!IO)] (
  %   io.print_line("Step " ++ string(!.NumSteps), !IO),
  %   io.print_line(array2d_to_string(!.SeaFloor, char_to_string, 0), !IO),
  %   io.nl(!IO)
  % ),
  !:NumSteps = !.NumSteps + 1,
  herd_step('>', (func((R - C)) = pair(R, C + 1)), !SeaFloor, EastHerdChanged),
  herd_step('v', (func((R - C)) = pair(R + 1, C)), !SeaFloor, SouthHerdChanged),
  (if or(EastHerdChanged, SouthHerdChanged) = no then
    true
  else
    simulate_until_herd_stops(!SeaFloor, !NumSteps)
  ).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  parse_sea_floor(Lines, SeaFloor),

  % Part 1
  simulate_until_herd_stops(SeaFloor, _, 0, NumSteps),
  io.print_line("Part 1: " ++ string(NumSteps), !IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "example",
    "input"
  ]),
  foldl(solve, Inputs, !IO).