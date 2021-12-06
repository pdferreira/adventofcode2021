:- module day06.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, array, solutions.
:- import_module utils.

:- type circular_array(T) ---> circular_array(zero_idx :: int, content :: array(T)).
:- inst carray_skel for circular_array/1 ---> circular_array(ground, uniq_array).
:- mode carray_uo == out(carray_skel).
:- mode carray_ui == in(carray_skel).
:- mode carray_di == di(carray_skel).

:- func init(int::in, T::in) = (circular_array(T)::carray_uo).
init(Size, Default) = circular_array(0, array.init(Size, Default)).

:- func copy(circular_array(T)::carray_ui) = (circular_array(T)::carray_uo).
copy(circular_array(ZeroIdx, Content)) = circular_array(ZeroIdx, array.copy(Content)).

:- func get(int::in, circular_array(T)::carray_ui) = (T::out) is semidet.
get(Idx, circular_array(ZeroIdx, Content)) = Content^elem(RealIdx) :-
  in_bounds(Content, Idx),
  RealIdx = (ZeroIdx + Idx) mod size(Content).

:- pred set(int::in, T::in, circular_array(T)::carray_di, circular_array(T)::carray_uo) is semidet.
set(Idx, Elem, !CircArr) :-
  circular_array(ZeroIdx, Content) = !.CircArr,
  in_bounds(Content, Idx),
  RealIdx = (ZeroIdx + Idx) mod size(Content),
  some [!Arr] (
    !:Arr = Content,
    array.set(RealIdx, Elem, !Arr),
    !:CircArr = circular_array(ZeroIdx, !.Arr)
  ).

:- pred shift_left(circular_array(T)::carray_di, circular_array(T)::carray_uo) is det.
shift_left(circular_array(ZeroIdx, Content), circular_array(NewZeroIdx, Content)) :-
  NewZeroIdx = (ZeroIdx + 1) mod size(Content).

:- type fish_lives == circular_array(int).

:- pred register_fish_lives(list(int)::in, fish_lives::carray_di, fish_lives::carray_uo) is semidet.
register_fish_lives([], !FishLivesArr).
register_fish_lives([F|Fs], !FishLivesArr) :-
  CurrFishes = get(F, !.FishLivesArr),
  set(F, CurrFishes + 1, !FishLivesArr),
  register_fish_lives(Fs, !FishLivesArr).

:- pred read_fish_lives(string::in, fish_lives::carray_uo) is semidet.
read_fish_lives(Line, FishLivesArr) :-
  FishLivesStr = split_at_string(",", Line),
  map(to_int, FishLivesStr, FishLives),
  some [!CircArr] (
    !:CircArr = init(9, 0),
    register_fish_lives(FishLives, !CircArr),
    FishLivesArr = !.CircArr
  ).

:- pred simulate_fish_lives(int::in, fish_lives::carray_di, fish_lives::carray_uo) is semidet.
simulate_fish_lives(Days, !FishLivesArr) :- (
  if Days = 0 then
    true
  else
    NumFishOnSpawnDay = get(0, !.FishLivesArr),
    % shift to next day, automatically leaving on day 8 the new spawns
    shift_left(!FishLivesArr),
    % add the parent fish to day 6
    set(6, NumFishOnSpawnDay + get(6, !.FishLivesArr), !FishLivesArr),
    simulate_fish_lives(Days - 1, !FishLivesArr)
).

:- func simulate_fish_growth(int::in, fish_lives::carray_ui) = (int::out) is semidet.
simulate_fish_growth(Days, FishLivesArr) = TotalFish :-
  some [!TmpFishLivesArr] (
    copy(FishLivesArr, !:TmpFishLivesArr),
    simulate_fish_lives(Days, !TmpFishLivesArr),
    TotalFish = foldl(plus, !.TmpFishLivesArr^content, 0)
  ).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    [L] = Lines,
    read_fish_lives(L, FishLivesArr)
  then
    % Part 1
    (if TotalFishP1 = simulate_fish_growth(80, FishLivesArr) then
      io.print_line("Part 1: " ++ string(TotalFishP1), !IO)
    else
      true
    ),

    % Part 2
    (if TotalFishP2 = simulate_fish_growth(256, FishLivesArr) then
      io.print_line("Part 2: " ++ string(TotalFishP2), !IO)
    else
      true
    )
  else
    true
  ).

main(!IO) :-
  solve("inputs/day06_example", !IO),
  io.nl(!IO),
  solve("inputs/day06_part1", !IO).
