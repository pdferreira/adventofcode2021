:- module day20.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, char, array, array2d, pair, solutions, exception.
:- import_module utils.

:- type position == pair(int, int).
:- type algorithm_spec == array(char).
:- type image == array2d(char).

:- func parse_algorithm(string) = algorithm_spec.
parse_algorithm(Line) = array.from_list(to_char_list(Line)).

:- func parse_image(list(string)::in, int::in) = (image::array2d_uo) is det.
parse_image([], ExpectedGrowth) = array2d.init(ExpectedGrowth * 2, ExpectedGrowth * 2, '.').
parse_image(Lines @ [L|_], ExpectedGrowth) = ImageArr :-
  LineLen = length(L),
  ImageLen = LineLen + ExpectedGrowth * 2,
  AffixLines = duplicate(ExpectedGrowth, duplicate(ImageLen, '.')),
  Affix = duplicate(ExpectedGrowth, '.'),
  CenterLines = map(func(Line) = Affix ++ to_char_list(Line) ++ Affix, Lines),
  ImageArr = array2d.from_lists(AffixLines ++ CenterLines ++ AffixLines).

:- pred parse_input(list(string)::in, int::in, algorithm_spec::out, image::array2d_uo) is semidet.
parse_input([SpecLine, ""|ImageLines], ExpectedGrowth, AlgorithmSpec, ImageArr) :-
  AlgorithmSpec = parse_algorithm(SpecLine),
  ImageArr = parse_image(ImageLines, ExpectedGrowth).

:- func pixel_to_binary_digit(char) = char is det.
pixel_to_binary_digit('.') = '0'.
pixel_to_binary_digit('#') = '1'.
pixel_to_binary_digit(_) = _ :- throw("unexpected").

:- func get_enhanced_value(algorithm_spec, image, int, int) = char.
get_enhanced_value(AlgoSpec, ImageArr, Row, Col) = AlgoSpec^elem(AlgoKey) :-
  bounds(ImageArr, MaxRow, MaxCol),
  solutions(adjacent_position(MaxRow, MaxCol, Row, Col), AdjPositions), % already sorted
  AllPositions = merge([pair(Row, Col)], AdjPositions),
  AlgoKeyBin = map(pipe2(elem2d(ImageArr), pixel_to_binary_digit), AllPositions),
  AlgoKey = det_base_string_to_int(2, from_char_list(AlgoKeyBin)).

:- pred enhance(algorithm_spec::in, image::in, int::in, int::in, image::array2d_di, image::array2d_uo) is det.
enhance(AlgoSpec, PrevImageArr, Row, Col, !ImageArr) :-
  bounds(PrevImageArr, MaxRow, MaxCol),
  set(Row, Col, get_enhanced_value(AlgoSpec, PrevImageArr, Row, Col), !ImageArr),
  (if Col + 1 < MaxCol then
    enhance(AlgoSpec, PrevImageArr, Row, Col + 1, !ImageArr)
  else if Row + 1 < MaxRow then
    enhance(AlgoSpec, PrevImageArr, Row + 1, 0, !ImageArr)
  else
    true 
  ).

:- pred enhance(algorithm_spec::in, image::array2d_di, image::array2d_uo) is det.
enhance(AlgoSpec, !ImageArr) :-
  copy(!.ImageArr, FrozenImageArr),
  enhance(AlgoSpec, FrozenImageArr, 0, 0, !ImageArr).

:- pred enhance(int::in, algorithm_spec::in, image::array2d_di, image::array2d_uo) is det.
enhance(N, AlgoSpec, !ImageArr) :-
  fold_up(
    (pred(_::in, ImageArrIn::array2d_di, ImageArrOut::array2d_uo) is det :- 
      enhance(AlgoSpec, ImageArrIn, ImageArrOut)
    ),
    1,
    N,
    !ImageArr
  ).

:- func count_light_pixels(image) = int.
count_light_pixels(ImageArr) = length(LightPixels) :-
  LightPixels = filter(unify('#'), condense(lists(ImageArr))).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  TimesToEnhance = 50,
  (if
    parse_input(Lines, TimesToEnhance + 1, AlgoSpec, ImageArr)
  then
    io.print_line(array2d_to_string(ImageArr, char_to_string, 0), !IO),
    io.nl(!IO),
    
    % Part 1
    enhance(2, AlgoSpec, ImageArr, EnhancedImageArr),
    io.print_line(array2d_to_string(EnhancedImageArr, char_to_string, 0), !IO),
    io.nl(!IO),

    io.format("Part 1: %i\r\n", [i(count_light_pixels(EnhancedImageArr))], !IO),

    % Part 2
    enhance(48, AlgoSpec, EnhancedImageArr, VeryEnhancedImageArr),
    io.format("Part 2: %i\r\n", [i(count_light_pixels(VeryEnhancedImageArr))], !IO)
  else
    true
  ),
  io.nl(!IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "example",
    "input"
  ]),
  foldl(solve, Inputs, !IO).