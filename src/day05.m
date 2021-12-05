:- module day05.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, map, solutions.
:- import_module utils.

:- type point ---> point(x :: int, y :: int).
:- type vent_line ---> vent_line(src :: point, dst :: point).
:- type vent_map == map(point, int).

:- pred read_point(string::in, point::out) is semidet.
read_point(PointStr, point(X, Y)) :-
  CoordStrs = split_at_char(',', PointStr),
  map(to_int, CoordStrs, [X, Y]).

:- pred read_vent_line(string::in, vent_line::out) is semidet.
read_vent_line(VentLineStr, vent_line(P1, P2)) :-
  PointStrs = split_at_string(" -> ", VentLineStr),
  map(read_point, PointStrs, [P1, P2]).

:- func signal(int) = int.
signal(N) = (
  if N > 0 then 1 
  else if N < 0 then -1 
  else 0
).

:- func delta(point, point) = point.
delta(P1, P2) = point(X, Y) :-
  % assume a unit vector, so just check the signals
  X = signal(P1^x - P2^x),
  Y = signal(P1^y - P2^y).

:- pred member(vent_line::in, point::out) is multi.
member(vent_line(P, _), P).
member(vent_line(P1, P2), MemberP) :-
  P1 \= P2,
  DeltaP = delta(P2, P1),
  NewP1 = point(P1^x + DeltaP^x, P1^y + DeltaP^y),
  member(vent_line(NewP1, P2), MemberP).

:- func add_vector_to_map(vent_line, vent_map) = vent_map.
add_vector_to_map(VentLine, Map) = ResMap :-
  Points = solutions(member(VentLine)),
  ResMap = foldl(
    (func(P, M) = (if search(M, P, Count) then
      det_update(M, P, Count + 1)
    else
      det_insert(M, P, 1)
    ) is det),
    Points,
    Map
  ). 

:- pred is_orthogonal(vent_line::in) is semidet.
is_orthogonal(vent_line(point(X, _), point(X, _))).
is_orthogonal(vent_line(point(_, Y), point(_, Y))).

:- func count_vent_overlaps(list(vent_line)) = int.
count_vent_overlaps(VentLines) = NumOverlaps :-
  Map = foldl(add_vector_to_map, VentLines, init),
  NumOverlaps = length(filter('=<'(2), values(Map))).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    map(read_vent_line, Lines, VentLines)
  then
    % Part 1
    filter(is_orthogonal, VentLines, NonDiagonalVentLines),
    NumOverlaps = count_vent_overlaps(NonDiagonalVentLines),
    io.print_line("Part 1: " ++ string(NumOverlaps), !IO),

    % Part 2
    NumFullOverlaps = count_vent_overlaps(VentLines),
    io.print_line("Part 2: " ++ string(NumFullOverlaps), !IO)
  else
    true
  ).

main(!IO) :-
  solve("inputs/day05_example", !IO),
  io.nl(!IO),
  solve("inputs/day05_part1", !IO).
