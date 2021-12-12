:- module day10.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, stack, map, char, solutions.
:- import_module utils.

:- pred matching_char(char, char).
:- mode matching_char(in, out) is semidet.
:- mode matching_char(out, in) is semidet.
:- mode matching_char(out, out) is multi.
matching_char('(', ')').
matching_char('[', ']').
matching_char('{', '}').
matching_char('<', '>').

:- func score_error_char(char) = int is semidet.
score_error_char(')') = 3.
score_error_char(']') = 57.
score_error_char('}') = 1197.
score_error_char('>') = 25137.

:- func score_autocomplete_char(char) = int is semidet.
score_autocomplete_char(')') = 1.
score_autocomplete_char(']') = 2.
score_autocomplete_char('}') = 3.
score_autocomplete_char('>') = 4.

:- func score_autocomplete_stack(stack(char)) = int is semidet.
score_autocomplete_stack(CloseStack) = Score :-
  CloseCharList = stack_to_list(CloseStack),
  foldl(
    (pred(CloseChar::in, CurrScore::in, NewScore::out) is semidet :- 
      score_autocomplete_char(CloseChar) = CharScore,
      NewScore = CurrScore * 5 + CharScore
    ),
    CloseCharList,
    0,
    Score
  ).

:- func score_wrong_chunks(func(list(char), stack(char)) = int, list(char), stack(char)) = int.
:- mode score_wrong_chunks(func(in, in) = out is semidet, in, in) = out is semidet.
:- mode score_wrong_chunks(func(in, in) = out is det, in, in) = out is det.
score_wrong_chunks(ScoreFn, [], CloseStack) = ScoreFn([], CloseStack).
score_wrong_chunks(ScoreFn, [C|Cs], CloseStack) = Score :-
  (if matching_char(C, ClosingC) then
    Score = score_wrong_chunks(ScoreFn, Cs, push(CloseStack, ClosingC))
  else if pop(C, CloseStack, NewCloseStack) then
    Score = score_wrong_chunks(ScoreFn, Cs, NewCloseStack)
  else
    Score = ScoreFn([C|Cs], CloseStack)
  ).

:- func score_syntax_error(list(char)) = int is semidet.
score_syntax_error(CharLine) = score_wrong_chunks(
  func([C|_], _) = score_error_char(C) is semidet,
  CharLine,
  stack.init
).

:- func score_autocomplete(list(char)) = int is semidet.
score_autocomplete(CharLine) = score_wrong_chunks(
  func([], CloseStack) = score_autocomplete_stack(CloseStack) is semidet,
  CharLine,
  stack.init
).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  CharLines = map(to_char_list, Lines),

  % Part 1
  filter_map(to_pred(score_syntax_error), CharLines, ErrorScores),
  io.print_line("Part 1: " ++ string(sum(ErrorScores)), !IO),

  % Part 2
  filter_map(to_pred(score_autocomplete), CharLines, AutocompleteScores),
  MiddleIndex = length(AutocompleteScores) / 2,
  MiddleScore = det_index0(sort(AutocompleteScores), MiddleIndex): int,
  io.print_line("Part 2: " ++ string(MiddleScore), !IO),

  io.nl(!IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "example1",
    "example2",
    "part1"
  ]),
  foldl(solve, Inputs, !IO).