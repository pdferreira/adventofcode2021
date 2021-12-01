:- module day01.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int.

:- type depth == int.

:- func count_increases(list(depth)) = int.
count_increases([]) = 0.
count_increases([_]) = 0.
count_increases([D1,D2|Ds]) = R :-
  I = (if D1 < D2 then 1 else 0),
  R = I + count_increases([D2|Ds]).

:- func sliding_windows(list(T), int) = list(list(T)).
sliding_windows(L, N) = WinLs :- (
  if (N >= 1, length(L) >= N) then
    WinLs = [take_upto(N, L) | sliding_windows(det_tail(L), N)]
  else
    WinLs = [] 
).

:- func sum(list(int)) = int.
sum([]) = 0.
sum([N|Ns]) = N + sum(Ns).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),

  read_lines(FileName, Lines, !IO),
  Report = map(string.det_to_int, Lines),
  
  Incs = count_increases(Report),
  io.print_line("Part 1: " ++ string(Incs), !IO),

  Windows = sliding_windows(Report, 3),
  WindowSumReport = map(sum, Windows),
  WindowIncs = count_increases(WindowSumReport),

  io.print_line("Part 2: " ++ string(WindowIncs), !IO).

main(!IO) :-
  solve("inputs/day01_example", !IO),
  io.nl(!IO),
  solve("inputs/day01_part1", !IO).

%%% File utilities

:- pred read_lines(list(string)::out, io::di, io::uo) is det.
read_lines(Lines, !IO) :-
  io.read_line_as_string(ReadRes, !IO),
  (if ReadRes = ok(Line) then
    Lines = [rstrip(Line)|Ls],
    read_lines(Ls, !IO)
  else
    Lines = []
  ).

:- pred read_lines(string::in, list(string)::out, io::di, io::uo) is det.
read_lines(FileName, Lines, !IO) :-
  see(FileName, SeeRes, !IO),
  (if SeeRes = ok then
    read_lines(Lines, !IO),
    seen(!IO)
  else
    Lines = []
  ).