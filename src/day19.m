:- module day19.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, char, set, maybe, pair, solutions, std_util.
:- import_module utils.

:- type point ---> point(x :: int, y :: int, z :: int).
:- type scanner ---> scanner(id :: int, beacons :: list(point), delta :: maybe(point)).

:- pred many(pred(A, list(T), list(T)), list(A), list(T), list(T)).
:- mode many(pred(out, in, out) is semidet, out, in, out) is semidet.
many(ParsePred, Result) -->
  ParsePred(Elem),
  (if many(ParsePred, Elems) then
    { Result = [Elem|Elems] }
  else
    { Result = [Elem] }
  ).

:- pred parse_point(point::out, list(string)::in, list(string)::out) is semidet.
parse_point(point(X, Y, Z)) -->
  [Line],
  { 
    map(to_int, split_at_char(',', Line), [X, Y, Z])
  }.

:- pred parse_scanner(scanner::out, list(string)::in, list(string)::out) is semidet.
parse_scanner(scanner(Id, Beacons, no)) -->
  [Header],
  { 
    remove_prefix("--- scanner ", Header, HeaderSuffix),
    remove_suffix(HeaderSuffix, " ---", IdStr),
    to_int(IdStr, Id)
  },
  many(parse_point, Beacons),
  (if [""] then [] else []).

:- func rotate_on_x(point) = point.
rotate_on_x(point(X, Y, Z)) = point(X, Z, -Y).

:- func rotate_on_y(point) = point.
rotate_on_y(point(X, Y, Z)) = point(Z, Y, -X).

:- func rotate_on_z(point) = point.
rotate_on_z(point(X, Y, Z)) = point(Y, -X, Z).

:- func map_beacons(func(point) = point, scanner) = scanner.
map_beacons(MapFn, scanner(Id, Points, Delta)) = scanner(Id, MappedPoints, Delta) :-
  MappedPoints = map(MapFn, Points).

:- pred generic_rotation(func(point) = point, scanner, scanner).
:- mode generic_rotation(in, in, out) is multi.
generic_rotation(RotateFn, Scanner, RotatedScanner) :-
  (
    RotatedScanner = Scanner  % (1, 2, 3)
  ;
    RotatedScanner = map_beacons(RotateFn, Scanner) % (1, -3, 2)
  ;
    RotatedScanner = map_beacons(pipe2(RotateFn, RotateFn), Scanner) % (1, -2, -3)
  ;
    RotatedScanner = map_beacons(pipe3(RotateFn, RotateFn, RotateFn), Scanner) % (1, 3, -2)
  ).

:- pred facings(scanner::in, list(scanner)::out) is det.
facings(Scanner, ScannerFacings) :-
  % facing right (x, y, z)
  FacingRight = Scanner, 
  % facing back (z, y, -x)
  FacingBack = map_beacons(rotate_on_y, Scanner),
  % facing left (-x, y, -z)
  FacingLeft = map_beacons(rotate_on_y, FacingBack),
  % facing front (-z, y, x)
  FacingFront = map_beacons(rotate_on_y, FacingLeft),
  % facing up (y, -x, z)
  FacingUp = map_beacons(rotate_on_z, Scanner),
  % facing down (-y, x, z)
  FacingDown = map_beacons(pipe2(rotate_on_z, rotate_on_z), FacingUp),
  
  ScannerFacings = [FacingRight, FacingBack, FacingLeft, FacingFront, FacingUp, FacingDown].

:- pred rotation(scanner::in, scanner::out) is nondet.
rotation(Scanner, RotatedScanner) :-
  facings(Scanner, ScannerFacings),
  member(ScannerFacing, ScannerFacings),
  generic_rotation(rotate_on_x, ScannerFacing, RotatedScanner).

:- func add_point(point, point) = point.
add_point(P1, P2) = point(P1^x + P2^x, P1^y + P2^y, P1^z + P2^z).

:- func minus_point(point, point) = point.
minus_point(P1, P2) = point(P1^x - P2^x, P1^y - P2^y, P1^z - P2^z).

:- pred find_overlapping_scanners(scanner::in, list(scanner)::in, list(scanner)::out) is det.
find_overlapping_scanners(scanner(Id, Points, _), OtherScanners, OverlappingScanners) :-
  % find all the other scanners (in any rotation) that overlaps with this scanner
  % by match any two points, adapting the coordinate system and checking if the overlap is >= 12
  filter_map(
    % for each OtherS in OtherScanners
    (pred(OtherS::in, TranslatedScanner3::out) is semidet :-
      Rotations = solutions(rotation(OtherS)),
      find_first_map(
        % for each rotation of OtherS
        (pred(scanner(OtherId, OtherPoints, _)::in, TranslatedScanner2::out) is semidet :-
          % now we have to try to match any point, and based on that match change the coords
          % to the first scanner's coord system and check if there're at least 12 points
          find_first_map(
            % for each point of the main scanner
            (pred(P::in, TranslatedScanner::out) is semidet :-
              find_first_map(
                % for each point of the second scanner
                (pred(OtherP::in, TranslatedScannerOut::out) is semidet :-
                  DeltaP = minus_point(OtherP, P),
                  TranslatedOtherPoints = map(func(OP) = minus_point(OP, DeltaP), OtherPoints),
                  CommonPoints = set.intersect(set.from_list(Points), set.from_list(TranslatedOtherPoints)),
                  count(CommonPoints) >= 12,
                  trace [io(!IO)] (
                    io.format("Overlap for %i and %i is %i and delta %s\r\n", [i(Id), i(OtherId), i(count(CommonPoints)), s(string(DeltaP))], !IO)
                  ),
                  TranslatedScannerOut = scanner(OtherId, TranslatedOtherPoints, yes(DeltaP))
                ),
                OtherPoints,
                TranslatedScanner
              )
            ),
            Points,
            TranslatedScanner2
          )
        ),
        remove_dups(Rotations),
        TranslatedScanner3
      )
    ), 
    OtherScanners,
    OverlappingScanners
  ).

:- func standardize_coordinates(list(scanner)) = list(scanner).
standardize_coordinates([]) = [].
standardize_coordinates([S|Ss]) = StandardSs :-
  find_overlapping_scanners(S, Ss, OverlappingScanners),
  OverlappingIds = map(func(OS) = OS^id, OverlappingScanners): list(int),
  SsWithoutAlreadySeen = filter(
    (pred(SomeS::in) is semidet :- not member(SomeS^id, OverlappingIds)), 
    Ss
  ),
  StandardSs = [S|standardize_coordinates(OverlappingScanners ++ SsWithoutAlreadySeen)].

:- func count_unique_beacons(list(scanner)) = int.
count_unique_beacons(Ss) = length(remove_dups(AllBeacons)) :-
  AllBeacons = condense(map(func(S) = S^beacons, Ss)).

:- func get_positions(list(scanner)) = list(point).
get_positions([]) = [].
get_positions([scanner(_, _, no)|Ss]) = [point(0, 0, 0)|get_positions(Ss)].
get_positions([scanner(_, _, yes(DeltaP))|Ss]) = [DeltaP|get_positions(Ss)].

:- func manhatan_dist(point, point) = int.
manhatan_dist(P1, P2) = abs(DX) + abs(DY) + abs(DZ) :-
  point(DX, DY, DZ) = minus_point(P1, P2).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    many(parse_scanner, Ss, Lines, [])
  then
    % Part 1
    StandardSs = standardize_coordinates(Ss),
    UniqueBeacons = count_unique_beacons(StandardSs),
    io.format("Part 1: %i\r\n", [i(UniqueBeacons)], !IO),

    % Part 2
    ScannerPositions = get_positions(StandardSs),
    Distances = map(func(Pair) = manhatan_dist(fst(Pair), snd(Pair)), combinations_unordered(ScannerPositions)),
    (if max(Distances) = MaxDist then
      io.format("Part 2: %i\r\n", [i(MaxDist)], !IO)
    else
      true
    )
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