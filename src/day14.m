:- module day14.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, int, list, map, pair, char.
:- import_module utils.

:- type element == char.
:- type element_p == pair(element, element).
:- type rules == map(element_p, element).
:- type polymer == list(element).
:- type polymer_rep == map(element_p, int).
:- type element_freq == map(element, int).

:- pred parse_rules(list(string)::in, rules::out) is semidet.
parse_rules(Lines, Rules) :-
  foldl(
    (pred(L::in, MapIn::in, MapOut::out) is semidet :-
      [Left, Right, ' ', '-', '>', ' ', New] = to_char_list(L),
      insert(pair(Left, Right), New, MapIn, MapOut) 
    ),
    Lines,
    map.init,
    Rules
  ).

:- pred synth_step(rules::in, element::in, polymer::in, polymer::out) is det.
synth_step(_, _, [], []).
synth_step(Rules, LookBehind, [E|Es], ElemsOut) :-
  (if search(Rules, pair(LookBehind, E), NewE) then
    ElemsOut = [NewE, E|RemElemsOut]
  else
    ElemsOut = [E|RemElemsOut]
  ),
  synth_step(Rules, E, Es, RemElemsOut).

:- pred synth_step(rules::in, polymer::in, polymer::out) is det.
synth_step(_, [], []).
synth_step(Rules, [E|Es], [E|RemElemsOut]) :-
  synth_step(Rules, E, Es, RemElemsOut).

:- pred synth(int::in, rules::in, polymer::in, polymer::out) is det.
synth(NumSteps, Rules, !Elems) :- fold_up(
  (pred(_::in, EsIn::in, EsOut::out) is det :- synth_step(Rules, EsIn, EsOut)),
  1,
  NumSteps,
  !Elems
).

:- pred synth_score(int::in, rules::in, polymer::in, int::out) is det.
synth_score(NumSteps, Rules, Elems, Score) :-
  synth(NumSteps, Rules, Elems, SynthResult),
  frequency(SynthResult, FreqMap),
  SortedValues = sort(values(FreqMap)),
  Score = det_last(SortedValues) - det_head(SortedValues).

:- pred polymer_to_rep(polymer::in, polymer_rep::in, polymer_rep::out, element_freq::in, element_freq::out) is det.
polymer_to_rep([], PolyRep, PolyRep, ElemFreq, ElemFreq).
polymer_to_rep([E], !PolyRep, !ElemFreq) :- increase_value(E, 1, !ElemFreq).
polymer_to_rep([E1,E2|Es], !PolyRep, !ElemFreq) :-
  (if search(!.PolyRep, pair(E1, E2), Count) then
    det_update(pair(E1, E2), Count + 1, !PolyRep)
  else
    det_insert(pair(E1, E2), 1, !PolyRep)
  ),
  increase_value(E1, 1, !ElemFreq),
  polymer_to_rep([E2|Es], !PolyRep, !ElemFreq).

:- pred polymer_to_rep(polymer::in, polymer_rep::out, element_freq::out) is det.
polymer_to_rep(Es, PolyRepOut, ElemFreqOut) :- polymer_to_rep(Es, map.init, PolyRepOut, map.init, ElemFreqOut).

:- pred increase_value(T::in, int::in, map(T, int)::in, map(T, int)::out) is det.
increase_value(Key, DeltaV, !Map) :-
    (if search(!.Map, Key, Value) then
      det_update(Key, Value + DeltaV, !Map)
    else
      det_insert(Key, DeltaV, !Map)
    ).

:- pred synth_pair_rep(rules::in, element_p::in, int::in, polymer_rep::in, polymer_rep::out, element_freq::in, element_freq::out) is det.
synth_pair_rep(Rules, OrigPair, OrigCount, !PolyRep, !ElemFreq) :-
  (if search(Rules, OrigPair, NewE) then
    E1 = fst(OrigPair),
    E2 = snd(OrigPair),
    % There were `OrigCount` pairs of (E1, E2)
    % So we now have `OrigCount` more (E1, NewE) pairs
    increase_value(pair(E1, NewE), OrigCount, !PolyRep),
    % And `OrigCount` more (NewE, E2) pairs
    increase_value(pair(NewE, E2), OrigCount, !PolyRep),
    % All (E1, E2) pairs now have a NewE between them, so don't register the previous pairs
    % But there're new NewE elements that need to be counted
    increase_value(NewE, OrigCount, !ElemFreq)
  else
    % Otherwise, the (E1, E2) pairs will remain unchanged, so we register them
    increase_value(OrigPair, OrigCount, !PolyRep)
  ).

:- pred synth_rep_step(rules::in, polymer_rep::in, polymer_rep::out, element_freq::in, element_freq::out) is det.
synth_rep_step(Rules, PolyRepIn, PolyRepOut, !ElemFreq) :-
  keys(PolyRepIn, ExistingPairsList),
  foldl2(
    (pred(Pair::in, TmpPolyRepIn::in, TmpPolyRepOut::out, TmpElemFreqIn::in, TmpElemFreqOut::out) is det :-
      lookup(PolyRepIn, Pair, Count),
      synth_pair_rep(Rules, Pair, Count, TmpPolyRepIn, TmpPolyRepOut, TmpElemFreqIn, TmpElemFreqOut)
    ),
    ExistingPairsList,
    map.init,
    PolyRepOut,
    !ElemFreq
  ).

:- pred synth_rep(int::in, rules::in, polymer_rep::in, polymer_rep::out, element_freq::in, element_freq::out) is det.
synth_rep(NumSteps, Rules, !PolyRep, !ElemFreq) :- fold_up2(
  (pred(_::in, TmpPolyRepIn::in, TmpPolyRepOut::out, TmpElemFreqIn::in, TmpElemFreqOut::out) is det :- 
    synth_rep_step(Rules, TmpPolyRepIn, TmpPolyRepOut, TmpElemFreqIn, TmpElemFreqOut)
  ),
  1,
  NumSteps,
  !PolyRep,
  !ElemFreq
).

:- pred synth_rep_score(int::in, rules::in, polymer::in, int::out) is det.
synth_rep_score(NumSteps, Rules, Polymer, Score) :-
  polymer_to_rep(Polymer, InitPolyRep, InitElemFreq),
  synth_rep(NumSteps, Rules, InitPolyRep, FinalPolyRep, InitElemFreq, FinalElemFreq),
  % trace [io(!IO)] io.print_line(map_to_string(FinalPolyRep): string, !IO),
  SortedValues = sort(values(FinalElemFreq)),
  Score = det_last(SortedValues) - det_head(SortedValues).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    [TemplateLine, _|RuleLines] = Lines,
    parse_rules(RuleLines, Rules)
  then
    Template = to_char_list(TemplateLine),
    
    % Part 1
    synth_score(10, Rules, Template, Part1Result),
    io.print_line("Part 1: " ++ string(Part1Result), !IO),

    % Part 2
    synth_rep_score(40, Rules, Template, Part2Result),
    io.print_line("Part 2: " ++ string(Part2Result), !IO),
    
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