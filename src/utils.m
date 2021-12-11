:- module utils.

:- interface.
:- import_module string, list, int, io, array.

:- pred read_lines(list(string)::out, io::di, io::uo) is det.
:- pred read_lines(string::in, list(string)::out, io::di, io::uo) is det.

:- func sum(list(int)) = int.
:- pred transpose(list(list(T))::in, list(list(T))::out) is det.
:- func transpose(list(list(T))) = list(list(T)) is det.

:- pred update(pred(A, A), array(A), array(A)).
:- mode update(pred(in, out) is semidet, array_di, array_uo) is det.
:- pred replace(A::in, A::in, array(A)::array_di, array(A)::array_uo) is det.

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

%%% Lists

sum([]) = 0.
sum([N|Ns]) = N + sum(Ns).

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
