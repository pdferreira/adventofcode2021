:- module utils.

:- interface.
:- import_module string, list, int, io, array.

%%% IO
:- pred read_lines(list(string)::out, io::di, io::uo) is det.
:- pred read_lines(string::in, list(string)::out, io::di, io::uo) is det.

%%% Math
:- type one_or_two(T) ---> one(T) ; two(T, T).
:- func sum(list(int)) = int.
:- func max(list(int)) = int is semidet.
:- func min(list(int)) = int is semidet.
:- func median(list(int)) = one_or_two(int) is semidet.
:- func arith_series_sum(int, int, int) = int.

%%% Lists
:- pred transpose(list(list(T))::in, list(list(T))::out) is det.
:- func transpose(list(list(T))) = list(list(T)) is det.

%%% Arrays
:- pred update(pred(A, A), array(A), array(A)).
:- mode update(pred(in, out) is semidet, array_di, array_uo) is det.
:- pred replace(A::in, A::in, array(A)::array_di, array(A)::array_uo) is det.

%%% Functions
:- func curry(func(A, B) = C) = (func(A) = (func(B) = C)).

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

% Functions

curry(Fn) = (func(Arg1) = (func(Arg2) = Fn(Arg1, Arg2))).