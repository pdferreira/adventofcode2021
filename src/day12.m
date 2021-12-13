:- module day12.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, digraph, set, solutions, bool.
:- import_module utils.

:- type cave ---> start_cave ; small_cave(string) ; big_cave(string) ; end_cave.

:- pred parse_cave(string::in, cave::out) is det.
parse_cave(CaveName, Cave) :-
  (if CaveName = "start" then
    Cave = start_cave
  else if CaveName = "end" then
    Cave = end_cave
  else if to_lower(CaveName) = CaveName then
    Cave = small_cave(CaveName)
  else
    Cave = big_cave(CaveName)
  ).

:- pred should_visit_once(cave::in) is semidet.
should_visit_once(start_cave).
should_visit_once(end_cave).
should_visit_once(small_cave(_)).

:- pred parse_path(string::in, digraph(cave)::in, digraph(cave)::out) is semidet.
parse_path(Line, !Graph) :-
  [CaveAName, CaveBName] = split_at_string("-", Line),
  parse_cave(CaveAName, CaveA),
  parse_cave(CaveBName, CaveB),
  add_vertex(CaveA, CaveAKey, !Graph),
  add_vertex(CaveB, CaveBKey, !Graph),
  add_edge(CaveAKey, CaveBKey, !Graph),
  add_edge(CaveBKey, CaveAKey, !Graph).

:- pred path(digraph_key(cave)::in, digraph_key(cave)::in, digraph(cave)::in, set(digraph_key(cave))::in, bool::in, list(cave)::out) is nondet.
path(SrcKey, DstKey, Graph, VisitedSmallCaveKeys, HasVisitedSmallTwice, [SrcCave|Path]) :-
  lookup_vertex(Graph, SrcKey, SrcCave),
  (if SrcKey = DstKey then
    Path = []
  else
    % add to visited set if small
    (if should_visit_once(SrcCave) then
      insert(SrcKey, VisitedSmallCaveKeys, NewVisitedSmallCaveKeys)
    else
      NewVisitedSmallCaveKeys = VisitedSmallCaveKeys
    ),
    % then follow the edges, skipping already visited small caves
    % with the exception if HasVisitedSmallTwice is still 'no'
    lookup_from(Graph, SrcKey, NextKeys),
    member(NextKey, NextKeys),
    (if not member(NextKey, NewVisitedSmallCaveKeys) then
      NewHasVisitedSmallTwice = HasVisitedSmallTwice
    else if 
      HasVisitedSmallTwice = no,
      lookup_vertex(Graph, NextKey, NextCave),
      not (NextCave = start_cave ; NextCave = end_cave)
    then
      NewHasVisitedSmallTwice = yes
    else
      fail
    ),
    path(NextKey, DstKey, Graph, NewVisitedSmallCaveKeys, NewHasVisitedSmallTwice, Path)
  ).

:- pred path(cave::in, cave::in, digraph(cave)::in, bool::in, list(cave)::out) is nondet.
path(SrcCave, DstCave, Graph, DisallowTwiceSmall, Path) :-
  lookup_key(Graph, SrcCave, SrcKey),
  lookup_key(Graph, DstCave, DstKey),
  path(SrcKey, DstKey, Graph, set.init, DisallowTwiceSmall, Path).

:- func cave_to_string(cave) = string.
cave_to_string(start_cave) = "start".
cave_to_string(end_cave) = "end".
cave_to_string(small_cave(Name)) = Name.
cave_to_string(big_cave(Name)) = Name.

:- func path_to_string(list(cave)) = string.
path_to_string(Cs) = join_list(" -> ", map(cave_to_string, Cs)). 

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    foldl(parse_path, Lines, digraph.init, Graph)
  then
    % Part 1
    solutions(path(start_cave, end_cave, Graph, yes), PathsP1),
    % io.print_line(join_list("\r\n", map(path_to_string, PathsP1)), !IO),
    io.print_line("Part 1: " ++ string(length(PathsP1): int), !IO),

    % Part 2
    solutions(path(start_cave, end_cave, Graph, no), PathsP2),
    % io.print_line(join_list("\r\n", map(path_to_string, PathsP2)), !IO),
    io.print_line("Part 2: " ++ string(length(PathsP2): int), !IO)
  else
    true
  ),
  io.nl(!IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "example1",
    "example2",
    "example3",
    "part1"
  ]),
  foldl(solve, Inputs, !IO).