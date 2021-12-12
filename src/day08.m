:- module day08.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, pair, set, solutions, map, char.
:- import_module utils.

:- type wire ---> wire_a ; wire_b ; wire_c ; wire_d ; wire_e ; wire_f ; wire_g.
:- type segment ---> seg_a ; seg_b ; seg_c ; seg_d ; seg_e ; seg_f ; seg_g.
:- type note == pair(list(string), list(string)).

:- pred parse_wire(char::in, wire::out) is semidet.
parse_wire(Ch, Wire) :- 
    WireName = "wire_" ++ from_char(Ch) ++ ".",
    io.read_from_string("parse_wire/1", WireName, length(WireName), ok(Wire), posn(1, 0, 0), _).

:- pred digit_display(list(segment), int).
:- mode digit_display(in, out) is semidet.
:- mode digit_display(out, in) is semidet.
digit_display([seg_a, seg_b, seg_c, seg_e, seg_f, seg_g], 0).
digit_display([seg_c, seg_f], 1).
digit_display([seg_a, seg_c, seg_d, seg_e, seg_g], 2).
digit_display([seg_a, seg_c, seg_d, seg_f, seg_g], 3).
digit_display([seg_b, seg_c, seg_d, seg_f], 4).
digit_display([seg_a, seg_b, seg_d, seg_f, seg_g], 5).
digit_display([seg_a, seg_b, seg_d, seg_e, seg_f, seg_g], 6).
digit_display([seg_a, seg_c, seg_f], 7).
digit_display([seg_a, seg_b, seg_c, seg_d, seg_e, seg_f, seg_g], 8).
digit_display([seg_a, seg_b, seg_c, seg_d, seg_f, seg_g], 9).

:- pred segments_to_digit(set(segment)::in, int::out) is semidet.
segments_to_digit(SegSet, N) :-
  digit_display(set.to_sorted_list(SegSet), N).

:- pred validate_assignment(map(wire, segment)::in, list(set(wire))::in) is semidet.
validate_assignment(_, []).
validate_assignment(Connections, [Ws|WsList]) :-
  SegSet = set.map(lookup(Connections), Ws),
  segments_to_digit(SegSet, _),
  validate_assignment(Connections, WsList).

:- pred valid_assignment(list(set(wire)), map(wire, segment)).
:- mode valid_assignment(in, out) is nondet.
valid_assignment(WsList, Connections) :-
  perm([wire_a, wire_b, wire_c, wire_d, wire_e, wire_f, wire_g], PossibleOrder),
  Connections = map.from_corresponding_lists(PossibleOrder, [seg_a, seg_b, seg_c, seg_d, seg_e, seg_f, seg_g]),
  validate_assignment(Connections, WsList).

:- func zip_with(func(A, B) = C, list(A), list(B)) = list(C) is semidet.
zip_with(_, [], []) = [].
zip_with(ZipElemFn, [X|Xs], [Y|Ys]) = [ZipElemFn(X, Y) | zip_with(ZipElemFn, Xs, Ys)]. 

:- pred read_note(string::in, note::out) is semidet.
read_note(Line, pair(SignalPatterns, OutputValues)) :-
  [SigPatternStr, OutputValueStr] = split_at_string(" | ", Line),
  SignalPatterns = split_at_string(" ", SigPatternStr),
  OutputValues = split_at_string(" ", OutputValueStr).

:- pred parse_wires(string::in, set(wire)::out) is semidet.
parse_wires(WireStr, WireSet) :-
  list.map(parse_wire, string.to_char_list(WireStr), WireList),
  WireSet = set.from_list(WireList).

:- pred analyse_note(note::in, int::out) is semidet.
analyse_note(Note, DisplayedN) :-
  % Find an assignment between Wires and Segments
  SigPatterns = fst(Note): list(string),
  list.map(parse_wires, SigPatterns, WsList),
  solutions(valid_assignment(WsList), [Connections]),
  
  % Apply the assignment to the outputs to get the digits
  OutputValues = snd(Note): list(string),
  list.map(
    utils.pipe3(
      parse_wires,
      set.map(lookup(Connections)),
      segments_to_digit
    ),
    OutputValues,
    DisplayedDigits
  ),
  DisplayedN = det_to_int(string.append_list(map(string, DisplayedDigits))).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    list.map(read_note, Lines, NotesList)
  then
    % Part 1
    CountMatchingVs = utils.pipe3(
      list.map(length),
      list.filter(list.contains([2, 4, 3, 7])),
      length
    ),
    OutputVsList = list.map(snd, NotesList),
    TotalCount: int = sum(list.map(CountMatchingVs, OutputVsList)),
    io.print_line("Part 1: " ++ string(TotalCount), !IO),
    
    % Part 2
    (if
      list.map(analyse_note, NotesList, DisplayedNs)
    then
      io.print_line("Part 2: " ++ string(sum(DisplayedNs)), !IO)
    else
      true
    )
  else
    true
  ).

main(!IO) :-
  solve("inputs/" ++ $module ++ "_example1", !IO),
  io.nl(!IO),
  solve("inputs/" ++ $module ++ "_example2", !IO),
  io.nl(!IO),
  solve("inputs/" ++ $module ++ "_part1", !IO).
