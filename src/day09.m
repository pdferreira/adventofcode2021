:- module day09.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is cc_multi.

:- implementation.
:- import_module string, list, int, array2d, char, solutions.
:- import_module utils.

:- type height == int.
:- type height_map == array2d(height).
:- type risk_level == int.
:- type basin_id == int.
:- type basin_map == array2d(basin_id).
:- type basin_sizes == list(int).

:- pred parse_height_map(list(string)::in, height_map::array2d_uo) is semidet.
parse_height_map(Lines, HeightMap) :- 
  map(
    utils.pipe2(
      to_pred(to_char_list),
      map(decimal_digit_to_int)
    ),
    Lines,
    DigitListOfLists
  ),
  HeightMap = array2d.from_lists(DigitListOfLists).

:- pred adjacent_point(height_map::in, int::in, int::in, height::out) is nondet.
adjacent_point(HeightMap, Row, Col, Height) :-
  bounds(HeightMap, MaxRow, MaxCol),
  (
    Row > 0, Height = HeightMap^elem(Row - 1, Col)
  ;
    Row + 1 < MaxRow, Height = HeightMap^elem(Row + 1, Col)
  ;
    Col > 0, Height = HeightMap^elem(Row, Col - 1)
  ;
    Col + 1 < MaxCol, Height = HeightMap^elem(Row, Col + 1)
  ).

:- pred lowest_point(height_map::in, int::in, int::in, height::out) is nondet.
lowest_point(HeightMap, Row, Col, LowestHeight) :-
  bounds(HeightMap, MaxRow, MaxCol),
  CurrHeight = HeightMap^elem(Row, Col),
  solutions(adjacent_point(HeightMap, Row, Col), AdjacentHeights),
  
  (
    % If this is the lowest height around, yield it
    all_true(pred(H::in) is semidet :- H > CurrHeight, AdjacentHeights), LowestHeight = CurrHeight
    % , trace [io(!IO)] io.print_line("(row: " ++ string(Row) ++ ", col: " ++ string(Col) ++ ") = " ++ string(CurrHeight), !IO)
  ;
    % Then continue searching for lowest points
    (if Col + 1 < MaxCol then
      lowest_point(HeightMap, Row, Col + 1, LowestHeight)
    else if Row + 1 < MaxRow then
      lowest_point(HeightMap, Row + 1, 0, LowestHeight)
    else
      false
    )
  ).

:- pred lowest_point(height_map::in, height::out) is nondet.
lowest_point(HeightMap, LowestHeight) :- lowest_point(HeightMap, 0, 0, LowestHeight).

:- func risk_level(height) = risk_level.
risk_level(Height) = Height + 1.

:- pred no_basin(basin_id).
:- mode no_basin(in) is semidet.
:- mode no_basin(out) is det.
no_basin(-1).

:- pred fill_basin(height_map, basin_id, int, int, basin_map, basin_map, int, int).
:- mode fill_basin(in, in, in, in, array2d_di, array2d_uo, in, out).
fill_basin(HeightMap, BasinId, Row, Col, !BasinMap, !BasinSize) :-
  (if 
    in_bounds(HeightMap, Row, Col),
    HeightMap^elem(Row, Col) \= 9,
    !.BasinMap^elem(Row, Col) = CurrBasinId,
    no_basin(CurrBasinId)
  then
    set(Row, Col, BasinId, !BasinMap),
    !:BasinSize = 1 + !.BasinSize,
    fill_basin(HeightMap, BasinId, Row, Col - 1, !BasinMap, !BasinSize),
    fill_basin(HeightMap, BasinId, Row, Col + 1, !BasinMap, !BasinSize),
    fill_basin(HeightMap, BasinId, Row - 1, Col, !BasinMap, !BasinSize),
    fill_basin(HeightMap, BasinId, Row + 1, Col, !BasinMap, !BasinSize)
  else
    true
  ).


:- pred find_basins(height_map, int, int, basin_map, basin_map, basin_sizes, basin_sizes).
:- mode find_basins(in, in, in, array2d_di, array2d_uo, in, out) is det.
find_basins(HeightMap, Row, Col, !BasinMap, !BasinSizes) :-
  bounds(HeightMap, MaxRow, MaxCol),
  CurrHeight = HeightMap^elem(Row, Col),
  % If 9 height move along
  (if CurrHeight = 9 then
    true
  % Else, if already in a basin, move along
  else if !.BasinMap^elem(Row, Col) = BasinId, not no_basin(BasinId) then
    true
  % Otherwise, is a new basin, flood fill
  else
    BasinId = length(!.BasinSizes),
    fill_basin(HeightMap, BasinId, Row, Col, !BasinMap, 0, NewBasinSize),
    !:BasinSizes = [NewBasinSize|!.BasinSizes]
  ),
  % Then continue to the next cell
  (if Col + 1 < MaxCol then
    find_basins(HeightMap, Row, Col + 1, !BasinMap, !BasinSizes)
  else if Row + 1 < MaxRow then
    find_basins(HeightMap, Row + 1, 0, !BasinMap, !BasinSizes)
  else
    true
  ).

:- pred find_basins(height_map::in, basin_map::array2d_uo, basin_sizes::out) is det.
find_basins(HeightMap, !:BasinMap, BasinSizes) :-
  bounds(HeightMap, MaxRow, MaxCol),
  no_basin(NoBasinId),
  !:BasinMap = init(MaxRow, MaxCol, NoBasinId),
  find_basins(HeightMap, 0, 0, !BasinMap, [], BasinSizes).

:- pred solve(string::in, io::di, io::uo) is cc_multi.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    parse_height_map(Lines, HeightMap)
  then
    % Part 1
    unsorted_solutions(lowest_point(HeightMap), LowestHeights),
    RiskLevel = sum(map(risk_level, LowestHeights)),
    io.print_line("Part 1: " ++ string(RiskLevel), !IO),

    % Part 2
    find_basins(HeightMap, _, BasinSizes),
    (if take(3, reverse(sort(BasinSizes)), LargestBasins) then
      SizeProduct = product(LargestBasins),
      io.print_line("Part 2: " ++ string(SizeProduct), !IO)
    else
      true
    )
  else
    true
  ).

main(!IO) :-
  solve("inputs/" ++ $module ++ "_example", !IO),
  io.nl(!IO),
  solve("inputs/" ++ $module ++ "_example2", !IO),
  io.nl(!IO),
  solve("inputs/" ++ $module ++ "_part1", !IO).