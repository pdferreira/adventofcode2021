:- module day15.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, int, list, char, pair, array2d, solutions, bool, exception.
:- import_module utils.

:- type risk == int.
:- type risk_map == array2d(risk).

:- pred parse_risk_map(list(string)::in, risk_map::array2d_uo) is det.
parse_risk_map(Lines, RiskMap) :-
  DigitMatrix = map(
    pipe2(to_char_list, map(det_decimal_digit_to_int)),
    Lines
  ),
  RiskMap = array2d.from_lists(DigitMatrix).

:- pred adjacent_position(int::in, int::in, int::in, int::in, pair(int, int)::out) is nondet.
adjacent_position(MaxRow, MaxCol, Row, Col, AdjPosition) :-
  (
    Col + 1 < MaxCol, AdjPosition = pair(Row, Col + 1)
  ;
    Row + 1 < MaxRow, AdjPosition = pair(Row + 1, Col)
  ;
    Col > 0, AdjPosition = pair(Row, Col - 1)
  ;
    Row > 0, AdjPosition = pair(Row - 1, Col)
  ).

:- func min_adjacent_risk(risk_map, int, int) = int is det.
min_adjacent_risk(RiskMap, Row, Col) = MinRisk :-
  bounds(RiskMap, MaxRow, MaxCol),
  solutions(day15.adjacent_position(MaxRow, MaxCol, Row, Col), AdjPositions),
  (MinRisk = min(map(elem2d(RiskMap), AdjPositions)) ; throw("Unexpected")).

:- pred transitive_risk_step(risk_map::in, int::in, int::in, risk_map::array2d_di, risk_map::array2d_uo, bool::out) is det.
transitive_risk_step(RiskMap, Row, Col, !TransitiveRiskMap, AnyChanges) :-
  MinAdjRisk = min_adjacent_risk(!.TransitiveRiskMap, Row, Col),
  BaseRisk = RiskMap^elem(Row, Col),
  NewRisk = MinAdjRisk + BaseRisk,
  (if !.TransitiveRiskMap^elem(Row, Col) = NewRisk then
    CurrChanged = no
  else
    CurrChanged = yes,
    set(Row, Col, NewRisk, !TransitiveRiskMap)
  ),
  bounds(RiskMap, MaxRow, MaxCol),
  (if Col + 1 < MaxCol then
    transitive_risk_step(RiskMap, Row, Col + 1, !TransitiveRiskMap, NextChanged)
  else if Row + 1 < MaxRow then
    transitive_risk_step(RiskMap, Row + 1, 0, !TransitiveRiskMap, NextChanged)
  else
    NextChanged = no
  ),
  AnyChanges = or(CurrChanged, NextChanged).

:- pred transitive_risk_fixpoint(risk_map::in, risk_map::array2d_di, risk_map::array2d_uo) is det.
transitive_risk_fixpoint(RiskMap, !TransitiveRiskMap) :-
  transitive_risk_step(RiskMap, 0, 1, !TransitiveRiskMap, AnyChanges),
  (if AnyChanges = yes then
    transitive_risk_fixpoint(RiskMap, !TransitiveRiskMap)
  else
    true
  ).

:- pred transitive_risk(risk_map::in, risk_map::out) is det.
transitive_risk(RiskMap, TransitiveRiskMapOut) :-
  bounds(RiskMap, MaxRow, MaxCol),
  TransitiveRiskMapIn = array2d.init(MaxRow, MaxCol, int.max_int),
  TransitiveRiskMapIn2 = TransitiveRiskMapIn^elem(0, 0) := 0,
  transitive_risk_fixpoint(RiskMap, TransitiveRiskMapIn2, TransitiveRiskMapOut).

:- func bold_digit(char) = char is semidet.
bold_digit('0') = '⓿'.
bold_digit('1') = '➊'.
bold_digit('2') = '➋'.
bold_digit('3') = '➌'.
bold_digit('4') = '➍'.
bold_digit('5') = '➎'.
bold_digit('6') = '➏'.
bold_digit('7') = '➐'.
bold_digit('8') = '➑'.
bold_digit('9') = '➒'.

:- pred draw_min_risk_path(risk_map::in, int::in, int::in, array2d(char)::array2d_di, array2d(char)::array2d_uo) is det.
draw_min_risk_path(TransitiveRiskMap, Row, Col, !DrawnMap) :-
  PathChar = (if bold_digit(!.DrawnMap^elem(Row, Col)) = BoldDigit then BoldDigit else '_'),
  set(Row, Col, PathChar, !DrawnMap),
  (if TransitiveRiskMap^elem(Row, Col) = 0 then
    true
  else
    bounds(TransitiveRiskMap, MaxRow, MaxCol),
    solutions(day15.adjacent_position(MaxRow, MaxCol, Row, Col), AdjPositions),
    (if MinPos = min_by(elem2d(TransitiveRiskMap), AdjPositions) then
      draw_min_risk_path(TransitiveRiskMap, fst(MinPos), snd(MinPos), !DrawnMap)
    else
      throw("unexpected")
    )
  ).

:- pred draw_min_risk_path(risk_map::in, risk_map::in, array2d(char)::array2d_uo) is det.
draw_min_risk_path(RiskMap, TransitiveRiskMap, DrawnMapOut) :-
  bounds(RiskMap, MaxRow, MaxCol),
  DrawnMapIn = array2d.from_lists(map(map(char.det_int_to_decimal_digit), array2d.lists(RiskMap))),
  draw_min_risk_path(TransitiveRiskMap, MaxRow - 1, MaxCol - 1, DrawnMapIn, DrawnMapOut).

:- pred fill_risk_tile(risk_map, int, int, int, int, int, risk_map, risk_map).
:- mode fill_risk_tile(in, in, in, in, in, in, array2d_di, array2d_uo) is det.
fill_risk_tile(TileTemplate, TemplateRow, TemplateCol, Row, Col, Delta, !FullRiskMap) :-
  TemplateV = TileTemplate^elem(TemplateRow, TemplateCol),
  NewV = ((TemplateV - 1 + Delta) mod 9) + 1,
  set(Row, Col, NewV, !FullRiskMap),
  bounds(TileTemplate, TemplateMaxRow, TemplateMaxCol),
  (if TemplateCol + 1 < TemplateMaxCol then
    fill_risk_tile(TileTemplate, TemplateRow, TemplateCol + 1, Row, Col + 1, Delta, !FullRiskMap)
  else if TemplateRow + 1 < TemplateMaxRow then
    fill_risk_tile(TileTemplate, TemplateRow + 1, 0, Row + 1, Col + 1 - TemplateMaxCol, Delta, !FullRiskMap)
  else
    true
  ).

:- pred fill_risk_tiles(risk_map, int, int, int, risk_map, risk_map).
:- mode fill_risk_tiles(in, in, in, in, array2d_di, array2d_uo) is det.
fill_risk_tiles(TileTemplate, Row, Col, Delta, !FullRiskMap) :-
  fill_risk_tile(TileTemplate, 0, 0, Row, Col, Delta, !FullRiskMap),
  bounds(!.FullRiskMap, MaxRow, MaxCol),
  bounds(TileTemplate, TileMaxRow, TileMaxCol),
  (if Col + TileMaxCol < MaxCol then
    fill_risk_tiles(TileTemplate, Row, Col + TileMaxCol, Delta + 1, !FullRiskMap)
  else if Row + TileMaxRow < MaxRow then
    fill_risk_tiles(TileTemplate, Row + TileMaxRow, 0, (Row / TileMaxRow) + 1, !FullRiskMap)
  else
    true
  ).

:- pred full_map(risk_map::in, risk_map::array2d_uo) is det.
full_map(TileTemplate, FullRiskMapOut) :-
  bounds(TileTemplate, MaxRow, MaxCol),
  FullRiskMapIn = array2d.init(MaxRow * 5, MaxCol * 5, 0),
  fill_risk_tiles(TileTemplate, 0, 0, 0, FullRiskMapIn, FullRiskMapOut).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  parse_risk_map(Lines, RiskMap),

  % Part 1
  transitive_risk(RiskMap, TransitiveRiskMap),
  
  % io.print_line(array2d_to_string(RiskMap, 2), !IO),
  % io.nl(!IO),

  % io.print_line(array2d_to_string(TransitiveRiskMap, 2), !IO),
  % io.nl(!IO),

  bounds(TransitiveRiskMap, MaxRow, MaxCol),
  Part1Result = TransitiveRiskMap^elem(MaxRow - 1, MaxCol - 1),
  io.print_line("Part 1: " ++ string(Part1Result), !IO),

  % Part 2
  full_map(RiskMap, FullRiskMap),
  transitive_risk(FullRiskMap, TransitiveFullRiskMap),
  
  % draw_min_risk_path(FullRiskMap, TransitiveFullRiskMap, FullDrawnRiskMap),
  % io.print_line(array2d_to_string(FullDrawnRiskMap, char_to_string, 1), !IO),
  % io.nl(!IO),

  bounds(TransitiveFullRiskMap, FullMaxRow, FullMaxCol),
  Part2Result = TransitiveFullRiskMap^elem(FullMaxRow - 1, FullMaxCol - 1),
    
  io.print_line("Part 2: " ++ string(Part2Result), !IO),
  io.nl(!IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "example",
    "example2",
    "part1"
  ]),
  foldl(solve, Inputs, !IO).