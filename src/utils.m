:- module utils.

:- interface.
:- import_module string, list, int, io, array, array2d, map, stack, pair, set.

%%% IO
:- pred read_lines(list(string)::out, io::di, io::uo) is det.
:- pred read_lines(string::in, list(string)::out, io::di, io::uo) is det.

%%% Math
:- type one_or_two(T) ---> one(T) ; two(T, T).
:- func sum(list(int)) = int.
:- func product(list(int)) = int.
:- func max(list(int)) = int.
% :- mode max(in(non_empty_list)) = out is det.
:- mode max(in) = out is semidet.
:- func min(list(int)) = int.
% :- mode min(in(non_empty_list)) = out is det.
:- mode min(in) = out is semidet.
:- func median(list(int)) = one_or_two(int) is semidet.
:- func arith_series_sum(int, int, int) = int.

%%% Lists
:- pred transpose(list(list(T))::in, list(list(T))::out) is det.
:- func transpose(list(list(T))) = list(list(T)) is det.
:- func zip_with(func(A, B) = C, list(A), list(B)) = list(C) is semidet.
:- func det_zip_with(func(A, B) = C, list(A), list(B)) = list(C).
:- pred frequency(list(A)::in, map(A, int)::out) is det.
:- func min_by(func(T) = int, list(T)) = T is semidet.
:- pred foldl_while(pred(T, A, A), list(T), A, A).
:- mode foldl_while(pred(in, in, out) is semidet, in, in, out) is semidet.
:- func combinations(list(T)) = list(pair(T, T)).
:- func combinations_unordered(list(T)) = list(pair(T, T)).
:- func list_to_string(list(T), func(T) = string) = string.

%%% Arrays
:- pred update(pred(A, A), array(A), array(A)).
:- mode update(pred(in, out) is semidet, array_di, array_uo) is det.
:- pred replace(A::in, A::in, array(A)::array_di, array(A)::array_uo) is det.
:- pred update2d(pred(A, A), array2d(A), array2d(A)).
:- mode update2d(pred(in, out) is semidet, array2d_di, array2d_uo) is det.
:- func array2d_to_string(array2d(T), int) = string.
:- func array2d_to_string(array2d(T), func(T) = string, int) = string.
:- func elem2d(array2d(T), pair(int, int)) = T is det.
:- pred adjacent_position(int::in, int::in, int::in, int::in, pair(int, int)::out) is nondet.

%%% Maps
:- func map_to_string(map(A, B)) = string.
:- pred increase_value(T::in, int::in, map(T, int)::in, map(T, int)::out) is det.

%%% Stacks
:- func stack_to_list(stack(T)) = list(T) is det.

%%% Sets
:- pred any_true(pred(T), set(T)).
:- mode any_true(pred(in) is semidet, in) is semidet.

%%% Pairs
:- func swap(pair(T1, T2)) = pair(T2, T1).

%%% Functions
:- func curry(func(A, B) = C) = (func(A) = (func(B) = C)).
:- func pipe2(func(A) = B, func(B) = C, A) = C.
:- mode pipe2(func(in) = out is det, func(in) = out is det, in) = out is det.
:- mode pipe2(func(in) = out is semidet, func(in) = out is semidet, in) = out is semidet.
:- mode pipe2(func(in) = out is semidet, func(in) = out is det, in) = out is semidet.
:- mode pipe2(func(in) = out is det, func(in) = out is semidet, in) = out is semidet.
:- func pipe3(func(A) = B, func(B) = C, func(C) = D, A) = D.
:- mode pipe3(func(in) = out is det, func(in) = out is det, func(in) = out is det, in) = out is det.
:- mode pipe3(func(in) = out is semidet, func(in) = out is semidet, func(in) = out is semidet, in) = out is semidet.
:- mode pipe3(func(in) = out is det, func(in) = out is semidet, func(in) = out is semidet, in) = out is semidet.
:- mode pipe3(func(in) = out is det, func(in) = out is det, func(in) = out is semidet, in) = out is semidet.
:- mode pipe3(func(in) = out is semidet, func(in) = out is det, func(in) = out is semidet, in) = out is semidet.
:- mode pipe3(func(in) = out is semidet, func(in) = out is det, func(in) = out is det, in) = out is semidet.
:- mode pipe3(func(in) = out is det, func(in) = out is semidet, func(in) = out is det, in) = out is semidet.
:- mode pipe3(func(in) = out is semidet, func(in) = out is semidet, func(in) = out is det, in) = out is semidet.
:- pred to_pred(func(A) = B, A, B).
:- mode to_pred(func(in) = out is det, in, out) is det.
:- mode to_pred(func(in) = out is semidet, in, out) is semidet.
:- func fixpoint(func(A) = A, A) = A.

%%% Predicates
:- pred pipe2(pred(A, B), pred(B, C), A, C).
:- mode pipe2(pred(in, out) is det, pred(in, out) is det, in, out) is det.
:- mode pipe2(pred(in, out) is det, pred(in, out) is semidet, in, out) is semidet.
:- mode pipe2(pred(in, out) is semidet, pred(in, out) is det, in, out) is semidet.
:- mode pipe2(pred(in, out) is semidet, pred(in, out) is semidet, in, out) is semidet.
:- pred pipe3(pred(A, B), pred(B, C), pred(C, D), A, D).
:- mode pipe3(pred(in, out) is det, pred(in, out) is det, pred(in, out) is det, in, out) is det.
:- mode pipe3(pred(in, out) is semidet, pred(in, out) is semidet, pred(in, out) is semidet, in, out) is semidet.
:- mode pipe3(pred(in, out) is det, pred(in, out) is semidet, pred(in, out) is semidet, in, out) is semidet.
:- mode pipe3(pred(in, out) is det, pred(in, out) is det, pred(in, out) is semidet, in, out) is semidet.
:- mode pipe3(pred(in, out) is semidet, pred(in, out) is det, pred(in, out) is semidet, in, out) is semidet.
:- mode pipe3(pred(in, out) is semidet, pred(in, out) is det, pred(in, out) is det, in, out) is semidet.
:- mode pipe3(pred(in, out) is det, pred(in, out) is semidet, pred(in, out) is det, in, out) is semidet.
:- mode pipe3(pred(in, out) is semidet, pred(in, out) is semidet, pred(in, out) is det, in, out) is semidet.

:- implementation.
:- import_module exception.

%%% IO

read_lines(Lines, !IO) :-
  io.read_line_as_string(ReadRes, !IO),
  (if ReadRes = ok(Line) then
    Lines = [rstrip(Line)|Ls],
    read_lines(Ls, !IO)
  else
    Lines = []
  ).

read_lines(FileName, Lines, !IO) :-
  see(FileName, SeeRes, !IO),
  (if SeeRes = ok then
    read_lines(Lines, !IO),
    seen(!IO)
  else
    Lines = []
  ).

%%% Math

sum([]) = 0.
sum([N|Ns]) = N + sum(Ns).

product(Ns) = foldl(func(N, Acc) = N * Acc, Ns, 1).

max(Ns @ [_|_]) = foldl(max, Ns, min_int).

min(Ns @ [_|_]) = foldl(min, Ns, max_int).

median(Ns @ [_|_]) = Median :-
  Len = length(Ns),
  MiddlePos = (Len / 2) + 1,
  (if odd(Len) then
    det_index1(Ns, MiddlePos, N),
    Median = one(N)
  else
    det_index1(Ns, MiddlePos - 1, N1),
    det_index1(Ns, MiddlePos, N2),
    Median = two(N1, N2)
  ).

arith_series_sum(FirstN, LastN, SeriesLen) = (SeriesLen * (FirstN + LastN)) / 2.

%%% Lists

transpose([], []).
transpose([Xs], Zs) :- chunk(Xs, 1, Zs).
transpose([X|Xs @ [_|_]], Zs) :-
  transpose(Xs, Ys),
  map_corresponding(cons, X, Ys, Zs).

transpose(Xs) = Zs :- transpose(Xs, Zs).

zip_with(_, [], []) = [].
zip_with(ZipElemFn, [X|Xs], [Y|Ys]) = [ZipElemFn(X, Y) | zip_with(ZipElemFn, Xs, Ys)].

det_zip_with(ZipElemFn, Xs, Ys) = zip_with(ZipElemFn, Xs, Ys).
det_zip_with(_, _, _) = _ :- throw("list sizes don't match").

frequency([], map.init).
frequency([X|Xs], FreqMap) :-
  frequency(Xs, InnerFreqMap),
  (if search(InnerFreqMap, X) = Count then
    FreqMap = det_update(InnerFreqMap, X, Count + 1)
  else
    FreqMap = det_insert(InnerFreqMap, X, 1)
  ).

min_by(_, [X]) = X.
min_by(ValueToCompareFn, [X1, X2|Xs]) = MinX :-
  NextMinX = min_by(ValueToCompareFn, [X2|Xs]),
  MinX = (if ValueToCompareFn(X1) =< ValueToCompareFn(NextMinX) then X1 else NextMinX).

foldl_while(_, [], !Acc).
foldl_while(Pred, [X|Xs], AccIn, AccOut) :-
  Pred(X, AccIn, PredAccOut),
  (if foldl_while(Pred, Xs, PredAccOut, NextAccOut) then
    AccOut = NextAccOut
  else
    AccOut = PredAccOut
  ).

combinations([]) = [].
combinations([X|Xs]) = map(pair(X), Xs) ++ map(func(A) = pair(A, X), Xs) ++ combinations(Xs).

combinations_unordered([]) = [].
combinations_unordered([X|Xs]) = map(pair(X), Xs) ++ combinations_unordered(Xs).

list_to_string(List, ElemToStringFn) = "[" ++ string.join_list(", ", map(ElemToStringFn, List)) ++ "]".

%%% Arrays

:- pred update_aux(pred(A, A), int, array(A), array(A)).
:- mode update_aux(pred(in, out) is semidet, in, array_di, array_uo) is det.
update_aux(Update, Idx, !Arr) :-
  (if in_bounds(!.Arr, Idx) then
    Elem = !.Arr^elem(Idx),
    (if Update(Elem, NewElem) then
      set(Idx, NewElem, !Arr)
    else
      true
    ),
    update_aux(Update, Idx + 1, !Arr)
  else
    true
  ).

update(Update, !Arr) :- update_aux(Update, 0, !Arr).

replace(A, B, !Arr) :- update(
  (pred(Elem::in, NewElem::out) is semidet :- Elem = A, NewElem = B),
  !Arr
).

:- pred update2d_aux(pred(A, A), int, int, array2d(A), array2d(A)).
:- mode update2d_aux(pred(in, out) is semidet, in, in, array2d_di, array2d_uo) is det.
update2d_aux(Update, Row, Col, !Arr2d) :-
  Elem = !.Arr2d^elem(Row, Col),
  (if Update(Elem, NewElem) then
    set(Row, Col, NewElem, !Arr2d)
  else
    true
  ),
  (if in_bounds(!.Arr2d, Row, Col + 1) then
    update2d_aux(Update, Row, Col + 1, !Arr2d)
  else if in_bounds(!.Arr2d, Row + 1, 0) then
    update2d_aux(Update, Row + 1, 0, !Arr2d)
  else
    true
  ).

update2d(Update, !Arr2d) :- update2d_aux(Update, 0, 0, !Arr2d).

elem2d(Array2d, Pos) = Array2d^elem(fst(Pos), snd(Pos)).

adjacent_position(MaxRow, MaxCol, Row, Col, AdjPosition) :-
  (
    Col + 1 < MaxCol, Row + 1 < MaxRow, AdjPosition = pair(Row + 1, Col + 1)
  ;
    Col + 1 < MaxCol, AdjPosition = pair(Row, Col + 1)
  ;
    Row + 1 < MaxRow, AdjPosition = pair(Row + 1, Col)
  ;
    Col > 0, AdjPosition = pair(Row, Col - 1)
  ;
    Row > 0, AdjPosition = pair(Row - 1, Col)
  ;
    Col > 0, Row + 1 < MaxRow, AdjPosition = pair(Row + 1, Col - 1)
  ;
    Col > 0, Row > 0, AdjPosition = pair(Row - 1, Col - 1)
  ;
    Col + 1 < MaxCol, Row > 0, AdjPosition = pair(Row - 1, Col + 1)
  ).

array2d_to_string(Array2d, PadSize) = array2d_to_string(Array2d, string, PadSize + 1).

array2d_to_string(Array2d, ElemToStringFn, PadSize) = string.join_list("\r\n", map(
    func(L) = string.join_list("", map(
      func(Elem) = pad_left(ElemToStringFn(Elem), ' ', PadSize),
      L
    )),
    array2d.lists(Array2d)
  )).

%%% Maps

map_to_string(Map) = "map(" ++ EntriesStr ++ ")" :-
  map.keys(Map, Keys),
  EntryStrList = list.map(func(K) = string(K) ++ " -> " ++ string(Map^det_elem(K)), Keys),
  EntriesStr = string.join_list(", ", EntryStrList).

increase_value(Key, DeltaV, !Map) :-
    (if search(!.Map, Key, Value) then
      det_update(Key, Value + DeltaV, !Map)
    else
      det_insert(Key, DeltaV, !Map)
    ).

%%% Stacks

stack_to_list(Stack) = List :-
  (if stack.is_empty(Stack) then
    List = []
  else
    det_pop(Elem, Stack, NewStack),
    List = [Elem|stack_to_list(NewStack)]
  ).

%%% Sets

any_true(Pred, Set) :-
  remove_least(Elem, Set, RemSet),
  (if Pred(Elem) then
    true
  else
    any_true(Pred, RemSet)
  ).

%%% Pairs

swap(P) = pair(snd(P), fst(P)). 

%%% Functions

curry(Fn) = (func(Arg1) = (func(Arg2) = Fn(Arg1, Arg2))).

pipe2(Fn1, Fn2, Arg1) = Fn2(Arg2) :- Fn1(Arg1) = Arg2.

pipe3(Fn1, Fn2, Fn3, Arg) = pipe2(Fn1, pipe2(Fn2, Fn3))(Arg).

to_pred(Fn, In, Out) :- Fn(In) = Out.

fixpoint(Fn, In) = Out :-
  TmpOut = Fn(In),
  (if TmpOut = In then
    Out = In
  else
    Out = fixpoint(Fn, TmpOut)
  ).

%%% Predicates

pipe2(Pred1, Pred2, In, Out) :- Pred1(In, Out1), Pred2(Out1, Out).

pipe3(Pred1, Pred2, Pred3, In, Out) :- pipe2(Pred1, pipe2(Pred2, Pred3), In, Out).