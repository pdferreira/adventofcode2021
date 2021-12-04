:- module day04.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, array.
:- import_module utils.

:- type number == int.
:- type matrix(T) == array(array(T)).
:- type bingo_cell ---> marked(number) ; unmarked(number).
:- type bingo_board == matrix(bingo_cell).

:- pred mark(number::in, int::in, bingo_board::array_di, bingo_board::array_uo) is det.
mark(N, Idx, !Board) :- 
  (if in_bounds(!.Board, Idx) then
    some [!Row] (
      !:Row = !.Board^elem(Idx),
      replace(unmarked(N), marked(N), !Row),
      set(Idx, !.Row, !Board)
    ),
    mark(N, Idx + 1, !Board)
  else
    true
  ).

:- pred mark(number::in, bingo_board::array_di, bingo_board::array_uo) is det.
mark(N, !Board) :- mark(N, 0, !Board).

:- func score_row(array(bingo_cell)) = int is det.
score_row(Row) = foldl(
  (func(Cell, InnerSum) = InnerSum + (if Cell = unmarked(N) then N else 0) is det),
  Row,
  0 
).

:- func score(number::in, bingo_board::in) = (int::out) is det.
score(LastMark, Board) = LastMark * foldl(
  (func(Row, Sum) = Sum + score_row(Row) is det),
  Board,
  0
).

:- pred is_marked(bingo_cell::in) is semidet.
is_marked(marked(_)).

:- pred won(bingo_board::in) is semidet.
won(Board) :-
  BoardToList = map(to_list, to_list(Board)) : list(list(bingo_cell)),
  (
    any_true(all_true(is_marked), BoardToList)
  ;
    any_true(all_true(is_marked), transpose(BoardToList))
  ).

:- func play(list(number), list(bingo_board)) = int is semidet. 
play(Ns, Bs) = play_aux(Ns, Bs, Bs).

:- func play_aux(list(number), list(bingo_board), list(bingo_board)) = int is semidet. 
play_aux([_|Ns], AllBoards, []) = play_aux(Ns, AllBoards, AllBoards).
play_aux([N|Ns], AllBoards, [B|Bs]) = Score :-
  some [!Board] (!:Board = B, mark(N, !.Board, _)),
  (if won(B) then
    Score = score(N, B)
  else
    Score = play_aux([N|Ns], AllBoards, Bs)
  ).

:- func play_to_lose(list(number), list(bingo_board)) = int is semidet. 
play_to_lose(Ns, Bs) = play_to_lose_aux(Ns, Bs, Bs).

:- func play_to_lose_aux(list(number), list(bingo_board), list(bingo_board)) = int is semidet. 
play_to_lose_aux([_|Ns], AllBoards, []) = play_to_lose_aux(Ns, AllBoards, AllBoards).
play_to_lose_aux([N|Ns], AllBoards, [B|Bs]) = Score :-
  some [!Board] (!:Board = B, mark(N, !.Board, _)),

  (if won(B) then
    delete_all(AllBoards, B, RemainingAllBoards),
    (if LatterWinner = play_to_lose_aux([N|Ns], RemainingAllBoards, Bs) then
      Score = LatterWinner
    else
      Score = score(N, B)
    )
  else
    Score = play_to_lose_aux([N|Ns], AllBoards, Bs)
  ).

:- func read_plays(string) = list(number).
read_plays(Line) = Plays :-
  Plays = map(det_to_int, words_separator(unify(','), Line)).

:- func read_board(list(string)) = bingo_board.
read_board(Lines) = Board :-
  WordLines = map(words, Lines),
  NumLines = map(map(det_to_int), WordLines),
  CellLines = map(map(func(X) = unmarked(X)), NumLines),
  Board = array.from_list(map(array.from_list, CellLines)).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    [L|Ls] = Lines,
    Plays = read_plays(L),
    NonEmptyLs = filter(not(is_empty), Ls),
    BoardChunks = chunk(NonEmptyLs, 5)
  then
    % Part 1
    (if 
      Boards = map(read_board, BoardChunks),
      Score = play(Plays, Boards)
    then
      io.print_line("Part 1: " ++ string(Score), !IO)
    else
      io.print_line("Part 1: failed", !IO)
    ),

    % Part 2
    (if 
      NewBoards = map(read_board, BoardChunks),
      LoserScore = play_to_lose(Plays, NewBoards)
    then
      io.print_line("Part 2: " ++ string(LoserScore), !IO)
    else
      io.print_line("Part 2: failed", !IO)
    )
  else
    true
  ).

main(!IO) :-
  solve("inputs/day04_example", !IO),
  io.nl(!IO),
  solve("inputs/day04_part1", !IO).
