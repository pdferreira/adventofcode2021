:- module day13.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, int, list, set, array2d.
:- import_module utils.

:- type point ---> point(x :: int, y :: int).
:- type paper_fold ---> horiz_paper_fold(int) ; vert_paper_fold(int).

:- pred parse_point(string::in, point::out) is semidet.
parse_point(Line, point(X, Y)) :-
  [XStr, YStr] = split_at_string(",", Line),
  to_int(XStr, X),
  to_int(YStr, Y).

:- pred parse_paper_fold(string::in, paper_fold::out) is semidet.
parse_paper_fold(Line, PaperFold) :-
  [_, CoordStr] = split_at_string(" along ", Line),
  [Coord, ValueStr] = split_at_string("=", CoordStr),
  to_int(ValueStr, Value),
  (if Coord = "x" then
    PaperFold = vert_paper_fold(Value)
  else if Coord = "y" then
    PaperFold = horiz_paper_fold(Value)
  else
    fail
  ).

:- pred apply_paper_fold(paper_fold::in, list(point)::in, list(point)::out) is det.
apply_paper_fold(horiz_paper_fold(FoldY), Ps, NewPs) :- 
  map(
    (pred(P::in, NewP::out) is det :-
      (if P^y > FoldY then 
        NewP = (P^y := FoldY - (P^y - FoldY))
      else
        NewP = P
      )
    ),
    Ps,
    NewPsWithDups
  ),
  % Remove duplicates
  NewPs = set.to_sorted_list(set.from_list(NewPsWithDups)).

apply_paper_fold(vert_paper_fold(FoldX), Ps, NewPs) :- 
  map(
    (pred(P::in, NewP::out) is det :-
      (if P^x > FoldX then 
        NewP = (P^x := FoldX - (P^x - FoldX))
      else
        NewP = P
      )
    ),
    Ps,
    NewPsWithDups
  ),
  % Remove duplicates
  NewPs = set.to_sorted_list(set.from_list(NewPsWithDups)).

:- func points_to_string(list(point)) = string is semidet.
points_to_string(Ps) = String :-
  MaxX = max(map(func(P) = P^x, Ps)): int,
  MaxY = max(map(func(P) = P^y, Ps)): int,
  EmptyArr2d = array2d.init(MaxY + 1, MaxX + 1, '.'),
  foldl(
    (pred(P::in, Arr2dIn::in, Arr2dOut::out) is semidet :-
      (if not in_bounds(Arr2dIn, P^y, P^x) then
        trace [io(!IO)] io.print_line(string(P) ++ " " ++ string(MaxX) ++ " " ++ string(MaxY), !IO)
      else
        true
      ),
      set(P^y, P^x, '#', Arr2dIn, Arr2dOut)
    ),
    Ps,
    EmptyArr2d,
    Arr2d
  ),
  String = array2d_to_string(Arr2d, char_to_string, 2).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    find_index_of_match(unify(""), Lines, 0, EmptyLineIndex),
    split_list(EmptyLineIndex, Lines, StartLines, [_|EndLines]),
    map(parse_point, StartLines, PointList),
    map(parse_paper_fold, EndLines, FoldList)
  then
    % Part 1
    (if [Fold|_] = FoldList then
      apply_paper_fold(Fold, PointList, FoldedPointList), 
      io.print_line("Part 1: " ++ string(length(FoldedPointList): int), !IO)
    else
      true
    ),

    % Part 2
    foldl(apply_paper_fold, FoldList, PointList, FullyFoldedPointList),
    (if PointMap = points_to_string(FullyFoldedPointList) then
      io.print_line("Part 2: ", !IO),
      io.print_line(PointMap, !IO)
    else
      true
    ),
    io.nl(!IO)
  else
    true
  ),
  io.nl(!IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "example",
    "part1"
  ]),
  foldl(solve, Inputs, !IO).