:- module day18.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, uint, char, maybe, pair, std_util.
:- import_module utils.

:- type tree(T) ---> leaf(T) ; node(left :: tree(T), right :: tree(T)).
:- type sf_num == tree(uint).

:- func tree_to_string(tree(T)) = string.
tree_to_string(leaf(V)) = string(V).
tree_to_string(node(LeftT, RightT)) = format("[%s,%s]", [
  s(tree_to_string(LeftT)),
  s(tree_to_string(RightT))
]).

:- pred parse_snailfish_num(sf_num::out, list(char)::in, list(char)::out) is semidet.
parse_snailfish_num(SFNum) -->
  (if ['['] then
    parse_snailfish_num(LeftSFNum),
    [','],
    parse_snailfish_num(RightSFNum),
    [']'],
    { SFNum = node(LeftSFNum, RightSFNum) }
  else
    [DigitChar],
    { 
      decimal_digit_to_int(DigitChar, Digit),
      uint.from_int(Digit, DigitU),
      SFNum = leaf(DigitU)
    }
  ).

:- pred parse_snailfish_num(string::in, sf_num::out) is semidet.
parse_snailfish_num(Line, SFNum) :- 
  parse_snailfish_num(SFNum, to_char_list(Line), []).

:- func add(sf_num, sf_num) = sf_num.
add(Left, Right) = reduce(node(Left, Right)).

:- func add_value_leftmost(sf_num, uint) = sf_num.
add_value_leftmost(leaf(V), DeltaV) = leaf(V + DeltaV).
add_value_leftmost(node(Left, Right), DeltaV) = node(NewLeft, Right) :-
  NewLeft = add_value_leftmost(Left, DeltaV).

:- func add_value_rightmost(sf_num, uint) = sf_num.
add_value_rightmost(leaf(V), DeltaV) = leaf(V + DeltaV).
add_value_rightmost(node(Left, Right), DeltaV) = node(Left, NewRight) :-
  NewRight = add_value_rightmost(Right, DeltaV).

:- pred explode_all_aux(uint::in, sf_num::in, sf_num::out, maybe(uint)::out, maybe(uint)::out) is det.
explode_all_aux(_, leaf(V), leaf(V), no, no).
explode_all_aux(Depth, node(Left, Right), ExplodedResult, NewCarryOverL, NewCarryOverR) :-
  (if Left = leaf(LeftV), Right = leaf(RightV), Depth = 4u then
    ExplodedResult = leaf(0u),
    NewCarryOverL = yes(LeftV),
    NewCarryOverR = yes(RightV)
  else
    explode_all_aux(Depth + 1u, Left, NewLeft, NewCarryOverL, CarryOverR),
    (if CarryOverR = yes(RV) then
      NewRight = add_value_leftmost(Right, RV)
    else
      NewRight = Right
    ),
    explode_all_aux(Depth + 1u, NewRight, FinalRight, CarryOverL, NewCarryOverR),
    (if CarryOverL = yes(LV) then
      FinalLeft = add_value_rightmost(NewLeft, LV)
    else
      FinalLeft = NewLeft
    ),
    ExplodedResult = node(FinalLeft, FinalRight)
  ).

:- func explode_all(sf_num) = sf_num.
explode_all(SFTreeIn) = SFTreeOut :- explode_all_aux(0u, SFTreeIn, SFTreeOut, _, _).

:- func split_first(sf_num) = sf_num.
split_first(leaf(V)) = SplitResult :-
  (if V >= 10u then
    SplitLeftV = V / 2u,
    SplitRightV = SplitLeftV + (if odd(V) then 1u else 0u),
    SplitResult = node(leaf(SplitLeftV), leaf(SplitRightV))
  else
    SplitResult = leaf(V)
  ).
split_first(node(Left, Right)) = SplitResult :-
  SplitLeft = split_first(Left),
  (if SplitLeft = Left then
    SplitRight = split_first(Right),
    SplitResult = node(Left, SplitRight)
  else
    SplitResult = node(SplitLeft, Right)
  ).

:- func reduce(sf_num) = sf_num.
reduce(SFNum) = fixpoint(pipe2(explode_all, split_first), SFNum).

:- func magnitude(sf_num) = uint.
magnitude(leaf(V)) = V.
magnitude(node(Left, Right)) = magnitude(Left) * 3u + magnitude(Right) * 2u.

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    map(parse_snailfish_num, Lines, SFNums @ [SFNum|RemSFNums])
  then
    % Part 1
    ResultNum = foldl(converse(add), RemSFNums, SFNum),
    io.print_line(tree_to_string(ResultNum), !IO),
    io.format("Part 1: %u\r\n", [u(magnitude(ResultNum))], !IO),

    % Part 2
    AddPairFn = (func(P) = add(fst(P), snd(P))),
    PossibleMagnitudes = map(pipe3(AddPairFn, magnitude, uint.cast_to_int), combinations(SFNums)),
    (if MaxPossibleMagnitude = max(PossibleMagnitudes) then
      io.format("Part 2: %i\r\n", [i(MaxPossibleMagnitude)], !IO)
    else
      true
    )
  else
    true
  ),
  io.nl(!IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "example1",
    "example2",
    "example3",
    "example4",
    "example5",
    "input"
  ]),
  foldl(solve, Inputs, !IO).