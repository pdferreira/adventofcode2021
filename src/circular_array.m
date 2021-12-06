
:- module circular_array.

:- interface.
:- import_module array.

:- type circular_array(T) ---> circular_array(zero_idx :: int, content :: array(T)).
:- inst carray_skel for circular_array/1 ---> circular_array(ground, uniq_array).
:- mode carray_uo == out(carray_skel).
:- mode carray_ui == in(carray_skel).
:- mode carray_di == di(carray_skel).

:- func init(int::in, T::in) = (circular_array(T)::carray_uo) is det.
:- func copy(circular_array(T)::carray_ui) = (circular_array(T)::carray_uo) is det.
:- func get(int::in, circular_array(T)::carray_ui) = (T::out) is semidet.
:- pred set(int::in, T::in, circular_array(T)::carray_di, circular_array(T)::carray_uo) is semidet.
:- pred shift_left(circular_array(T)::carray_di, circular_array(T)::carray_uo) is det.

:- implementation.
:- import_module int.

init(Size, Default) = circular_array(0, array.init(Size, Default)).

copy(circular_array(ZeroIdx, Content)) = circular_array(ZeroIdx, array.copy(Content)).

get(Idx, circular_array(ZeroIdx, Content)) = Content^elem(RealIdx) :-
  in_bounds(Content, Idx),
  RealIdx = (ZeroIdx + Idx) mod size(Content).

set(Idx, Elem, !CircArr) :-
  circular_array(ZeroIdx, Content) = !.CircArr,
  in_bounds(Content, Idx),
  RealIdx = (ZeroIdx + Idx) mod size(Content),
  some [!Arr] (
    !:Arr = Content,
    array.set(RealIdx, Elem, !Arr),
    !:CircArr = circular_array(ZeroIdx, !.Arr)
  ).

shift_left(circular_array(ZeroIdx, Content), circular_array(NewZeroIdx, Content)) :-
  NewZeroIdx = (ZeroIdx + 1) mod size(Content).