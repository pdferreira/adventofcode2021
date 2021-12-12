:- module utils.

:- interface.
:- import_module string, list, int, io, array, array2d, map.

%%% IO
:- pred read_lines(list(string)::out, io::di, io::uo) is det.
:- pred read_lines(string::in, list(string)::out, io::di, io::uo) is det.

%%% Math
:- type one_or_two(T) ---> one(T) ; two(T, T).
:- func sum(list(int)) = int.
:- func product(list(int)) = int.
:- func max(list(int)) = int is semidet.
:- func min(list(int)) = int is semidet.
:- func median(list(int)) = one_or_two(int) is semidet.
:- func arith_series_sum(int, int, int) = int.

%%% Lists
:- pred transpose(list(list(T))::in, list(list(T))::out) is det.
:- func transpose(list(list(T))) = list(list(T)) is det.
:- func zip_with(func(A, B) = C, list(A), list(B)) = list(C) is semidet.

%%% Arrays
:- pred update(pred(A, A), array(A), array(A)).
:- mode update(pred(in, out) is semidet, array_di, array_uo) is det.
:- pred replace(A::in, A::in, array(A)::array_di, array(A)::array_uo) is det.
:- func array2d_to_string(array2d(T), int) = string.

%%% Maps
:- func map_to_string(map(A, B)) = string.

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

array2d_to_string(Array2d, PadSize) = string.join_list("\r\n", map(
    func(L) = string.join_list(" ", map(
      func(Elem) = pad_left(string(Elem), ' ', PadSize),
      L
    )),
    array2d.lists(Array2d)
  )).

%%% Maps

map_to_string(Map) = "map(" ++ EntriesStr ++ ")" :-
  map.keys(Map, Keys),
  EntryStrList = list.map(func(K) = string(K) ++ " -> " ++ string(Map^det_elem(K)), Keys),
  EntriesStr = string.join_list(", ", EntryStrList).

%%% Functions

curry(Fn) = (func(Arg1) = (func(Arg2) = Fn(Arg1, Arg2))).

pipe2(Fn1, Fn2, Arg1) = Fn2(Arg2) :- Fn1(Arg1) = Arg2.

pipe3(Fn1, Fn2, Fn3, Arg) = pipe2(Fn1, pipe2(Fn2, Fn3))(Arg).

to_pred(Fn, In, Out) :- Fn(In) = Out.

%%% Predicates

pipe2(Pred1, Pred2, In, Out) :- Pred1(In, Out1), Pred2(Out1, Out).

pipe3(Pred1, Pred2, Pred3, In, Out) :- pipe2(Pred1, pipe2(Pred2, Pred3), In, Out).