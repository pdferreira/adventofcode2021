:- module day23.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, map, solutions, pqueue, pair, exception, bool.
:- import_module utils.

:- type stack(T) == list(T).
:- type amphipod_type ---> amber ; bronze ; copper ; desert.
:- type burrow ---> burrow(
  rooms :: list(stack(amphipod_type)),
  room_size :: int,
  hallway :: map(int, amphipod_type)
).
:- type amphipod_move --->
  room_to_hallway(/*room_number ::*/ int, /*hallway_position ::*/ int) ;
  hallway_to_room(/*hallway_position ::*/ int, /*room_number ::*/ int) ;
  room_to_room(/*source_room_number ::*/ int, /*target_room_number ::*/ int).
:- type search_state ---> search_state(burrow, list(pair(int, amphipod_move)), int).

:- pred apply_move(amphipod_move::in, burrow::in, burrow::out) is semidet.
apply_move(room_to_hallway(RoomNum, HallwayPos), !Burrow) :-
  index1(!.Burrow^rooms, RoomNum, [A|As]),
  !Burrow^rooms := det_replace_nth(!.Burrow^rooms, RoomNum, As),
  !Burrow^hallway := map.insert(!.Burrow^hallway, HallwayPos, A).

apply_move(hallway_to_room(HallwayPos, RoomNum), !Burrow) :-
  remove(HallwayPos, AType, !.Burrow^hallway, NewHallway),
  !Burrow^hallway := NewHallway,
  index1(!.Burrow^rooms, RoomNum, As),
  !Burrow^rooms := det_replace_nth(!.Burrow^rooms, RoomNum, [AType|As]).

apply_move(room_to_room(SourceRoomNum, TargetRoomNum), !Burrow) :-
  index1(!.Burrow^rooms, SourceRoomNum, [A|As]),
  !Burrow^rooms := det_replace_nth(!.Burrow^rooms, SourceRoomNum, As),
  index1(!.Burrow^rooms, TargetRoomNum, TargetAs),
  !Burrow^rooms := det_replace_nth(!.Burrow^rooms, TargetRoomNum, [A|TargetAs]).

:- pred target_room(amphipod_type, int).
:- mode target_room(in, out) is det.
:- mode target_room(out, in) is semidet.
target_room(amber, 1).
target_room(bronze, 2).
target_room(copper, 3).
target_room(desert, 4).

:- func amphipod_energy_cost(amphipod_type) = int.
amphipod_energy_cost(amber) = 1.
amphipod_energy_cost(bronze) = 10.
amphipod_energy_cost(copper) = 100.
amphipod_energy_cost(desert) = 1000.

:- pragma promise_pure(room_entrance_position/2).
:- pred room_entrance_position(int, int).
:- mode room_entrance_position(in, out) is semidet.
:- mode room_entrance_position(out, in) is semidet.
room_entrance_position(RoomNumber::in, EntrancePos::out) :-
  RoomNumber >= 1,
  RoomNumber =< 4,
  EntrancePos = 2 * RoomNumber + 1.
room_entrance_position(RoomNumber::out, EntrancePos::in) :-
  odd(EntrancePos),
  EntrancePos >= 3,
  EntrancePos =< 10,
  RoomNumber = (EntrancePos - 1) / 2.

:- pred hallway_has_path(map(int, amphipod_type)::in, int::in, int::in, int::out) is semidet.
hallway_has_path(Hallway, SourcePos, TargetPos, NumMoves) :-
  not contains(Hallway, TargetPos),
  (if SourcePos < TargetPos then
    lower_bound_search(Hallway, TargetPos, NextOccupiedPos, _) => (NextOccupiedPos =< SourcePos),
    NumMoves = TargetPos - SourcePos
  else
    upper_bound_search(Hallway, TargetPos, NextOccupiedPos, _) => (NextOccupiedPos >= SourcePos),
    NumMoves = SourcePos - TargetPos
  ).

:- func free_hallway_positions(map(int, amphipod_type), int, int) = list(int).
free_hallway_positions(Hallway, From, To) = FreePositions :-
  AllPositionsExceptRoomEntrances = delete_elems(From .. To, [3, 5, 7, 9]),
  FreePositions = negated_filter(contains(Hallway), AllPositionsExceptRoomEntrances).

:- pred target_room(amphipod_type::in, burrow::in, int::out, stack(amphipod_type)::out, int::out, bool::out) is semidet.
target_room(AType, Burrow, TargetRoomNumber, TargetRoom, TargetEntrancePos, IsEligible) :- 
  target_room(AType, TargetRoomNumber),
  TargetRoom = det_index1(Burrow^rooms, TargetRoomNumber),
  room_entrance_position(TargetRoomNumber, TargetEntrancePos),
  IsEligible = (if all_true(unify(AType), TargetRoom) then yes else no).
    
:- pred valid_move(burrow::in, pair(int, amphipod_move)::out) is nondet.
valid_move(Burrow, pair(EnergyCost, PossibleMove)) :-
  (
    % For each hallway position with an amphipod
    member(Burrow^hallway, HallwayPos, AType),
    % Whose target room is eligible
    target_room(AType, Burrow, TargetRoomNumber, TargetRoom, TargetEntrancePos, yes),
    % Try to send it to its room
    % if the room has space
    TargetRoomFill = length(TargetRoom),
    TargetRoomFill < Burrow^room_size,
    % and there's a free path to it
    hallway_has_path(Burrow^hallway, HallwayPos, TargetEntrancePos, NumHallwayMoves),
    NumMoves = NumHallwayMoves + (Burrow^room_size - TargetRoomFill),
    PossibleMove = hallway_to_room(HallwayPos, TargetRoomNumber),
    EnergyCost = NumMoves * amphipod_energy_cost(AType)
  ;
    % For each room
    member_index0(Room, Burrow^rooms, RoomIdx),
    RoomNumber = RoomIdx + 1,
    % That has amphipods that don't belong there
    target_room(TargetAType, RoomNumber),
    not all_true(unify(TargetAType), Room),
    [AType|_] = Room,
    room_entrance_position(RoomNumber, SourceEntrancePos),
    SourceRoomFill = length(Room),
    target_room(AType, Burrow, TargetRoomNumber, TargetRoom, TargetEntrancePos, IsEligible),
    (if
      % Try to send the amphipod closest to the entrance to its target room
      % if it has only target-type amphipods
      IsEligible = yes,
      % it has space
      TargetRoomFill = length(TargetRoom),
      TargetRoomFill < Burrow^room_size,
      % and the hallway is free
      hallway_has_path(Burrow^hallway, SourceEntrancePos, TargetEntrancePos, NumHallwayMoves),
      NumMoves = NumHallwayMoves + (Burrow^room_size - SourceRoomFill + 1) + (Burrow^room_size - TargetRoomFill)
    then
      PossibleMove = room_to_room(RoomNumber, TargetRoomNumber),
      EnergyCost = NumMoves * amphipod_energy_cost(AType)
    else
      % Otherwise, try to send the amphipod to the hallway
      member(HallwayPos, free_hallway_positions(Burrow^hallway, 1, 11)),
      hallway_has_path(Burrow^hallway, SourceEntrancePos, HallwayPos, NumHallwayMoves),

      % But only if it doesn't block its own entrance forever
      % i.e. the amphipods that need to leave its room don't need to go to rooms
      % that are blocked by it OR they could all possibly move outside, while leaving it space to enter
      negated_filter(unify(AType), TargetRoom, AmphipodsThatNeedToLeave),
      filter(
        (pred(ATypeToFilter::in) is semidet :-
          target_room(ATypeToFilter, RoomNumToFilter),
          room_entrance_position(RoomNumToFilter, Pos),
          hallway_has_path(Burrow^hallway, TargetEntrancePos, Pos, _), % if it couldn't leave before, this move won't change that
          not hallway_has_path(map.insert(Burrow^hallway, HallwayPos, AType), TargetEntrancePos, Pos, _)
        ),
        AmphipodsThatNeedToLeave,
        AmphipodsThatCantLeave
      ),
      (if AmphipodsThatCantLeave = [] then
        true
      else 
        AvailableEscapePositions = (if HallwayPos < TargetEntrancePos then
          free_hallway_positions(Burrow^hallway, TargetEntrancePos + 1, 11)
        else
          free_hallway_positions(Burrow^hallway, 1, TargetEntrancePos - 1)
        ),
        length(AmphipodsThatCantLeave) =< length(AvailableEscapePositions)
      ),
      NumMoves = NumHallwayMoves + (Burrow^room_size - SourceRoomFill + 1),
      PossibleMove = room_to_hallway(RoomNumber, HallwayPos),
      EnergyCost = NumMoves * amphipod_energy_cost(AType)
    )
  ).

:- pred valid_next_state(search_state::in, search_state::out) is nondet.
valid_next_state(search_state(CurrBurrow, Moves, EnergySpent), search_state(NextBurrow, [PossibleMovePair|Moves], NextEnergySpent)) :-
  % Instead of yielding all possible moves, in all orders
  % Trim the search space by yielding a single move to a room, if available
  % It's always a no-brainer move and doesn't cut any possibility
  solutions(valid_move(CurrBurrow), PossibleMovesWithCost),
  (if 
    find_first_match(
      (pred(MoveP::in) is semidet :- snd(MoveP) = hallway_to_room(_, _) ; snd(MoveP) = room_to_room(_, _)),
      PossibleMovesWithCost,
      FirstPossibleMoveToRoom
    ) 
  then
    PossibleMovePair = FirstPossibleMoveToRoom
  else
    % Otherwise, we want to yield every available move to the hallway
    member(PossibleMovePair, PossibleMovesWithCost)
  ),
  MoveEnergyCost = fst(PossibleMovePair),
  PossibleMove = snd(PossibleMovePair),
  apply_move(PossibleMove, CurrBurrow, NextBurrow),
  NextEnergySpent = EnergySpent + MoveEnergyCost.

:- pred is_burrow_organized(burrow::in) is semidet.
is_burrow_organized(Burrow) :-
  is_empty(Burrow^hallway),
  all_true_corresponding(
    (pred(Room::in, RoomNumber::in) is semidet :-
      target_room(AType, RoomNumber),
      all_true(unify(AType), Room) 
    ),
    Burrow^rooms,
    1 .. length(Burrow^rooms)
  ).

:- func missing_energy_heuristic(burrow) = int.
missing_energy_heuristic(Burrow) = MinEnergyCost :-
  % The heuristic is the cost of moving all amphipods to their rooms
  % ignoring obstacles/restrictions (thus a lower-bound, making it admissible)

  % Count the cost of moving the hallway-amphipods to their rooms
  map.foldl(
    (pred(Pos::in, AType::in, HCosts::in, NewHCosts::out) is det :-
      target_room(AType, TargetRoomNumber),
      (if
        room_entrance_position(TargetRoomNumber, TargetPos),
        hallway_has_path(map.init, Pos, TargetPos, NumHallwayMoves) 
      then
        % at least have to move in the corridor and enter
        HCost = (NumHallwayMoves + 1) * amphipod_energy_cost(AType)
      else
        throw("unexpected")
      ),
      NewHCosts = HCost + HCosts
    ),
    Burrow^hallway, 
    0, 
    HallwayMoveCost
  ),

  % Count the cost of moving room-amphipods on the wrong rooms to their rooms
  list.foldl_corresponding(
    (pred(Room::in, RoomNumber::in, RCosts::in, NewRCosts::out) is det :-
      (if target_room(AType, RoomNumber), all_true(unify(AType), Room) then
        RCost = 0
      else if room_entrance_position(RoomNumber, SourceHallwayPos) then
        list.foldl_corresponding(
          (pred(CurrAType::in, PosInRoom::in, Costs::in, NewCosts::out) is det :-
            target_room(CurrAType, TargetRoomNumber),
            (if 
              room_entrance_position(TargetRoomNumber, TargetHallwayPos),
              hallway_has_path(map.init, SourceHallwayPos, TargetHallwayPos, NumHallwayMoves2)
            then
              NumRoomOutMoves = Burrow^room_size - PosInRoom + 1,
              NumRoomInMoves = 1, % at least to enter the room 
              C = (NumRoomOutMoves + NumHallwayMoves2 + NumRoomInMoves) * amphipod_energy_cost(CurrAType)
            else
              C = 0
            ),
            NewCosts = C + Costs
          ), 
          Room,
          reverse(1 .. length(Room)),
          0,
          RCost
        )
      else
        throw("unexpected")
      ),
      NewRCosts = RCost + RCosts
    ),
    Burrow^rooms,
    1 .. length(Burrow^rooms),
    0,
    RoomMoveCost
  ),
  MinEnergyCost = HallwayMoveCost + RoomMoveCost.

% basically A*, keeping track of the moves list for easier troubleshooting only
:- pred find_min_energy_moves_aux(pqueue(int, search_state)::in, search_state::out) is semidet. 
find_min_energy_moves_aux(StatesToExplore, FinalState) :-
  remove(_, CurrState, StatesToExplore, RemainingStates),
  CurrState = search_state(CurrBurrow, _, _),
  (if is_burrow_organized(CurrBurrow) then
    FinalState = CurrState
  else
    solutions(valid_next_state(CurrState), PossibleNextStates),
    foldl(
      (pred(NextState::in, StatesIn::in, StatesOut::out) is det :-
        NextState = search_state(NextBurrow, _, NextEnergySpent),
        NextEnergyEstimate = NextEnergySpent + missing_energy_heuristic(NextBurrow),
        pqueue.insert(NextEnergyEstimate, NextState, StatesIn, StatesOut)
      ), 
      PossibleNextStates,
      RemainingStates,
      NextStatesToExplore
    ),
    find_min_energy_moves_aux(NextStatesToExplore, FinalState)
  ).

:- pred find_min_energy_moves(burrow::in, list(pair(int, amphipod_move))::out, int::out) is semidet.
find_min_energy_moves(Burrow, Moves, EnergySpent) :-
  InitialStates = pqueue.insert(pqueue.init, missing_energy_heuristic(Burrow), search_state(Burrow, [], 0)),
  find_min_energy_moves_aux(InitialStates, search_state(_, Moves, EnergySpent)).

:- func extend_burrow(burrow) = burrow.
extend_burrow(Burrow) = burrow(NewRooms, 4, Burrow^hallway) :-
  (if Burrow^room_size = 2, length(Burrow^rooms) = 4 then
    FirstLine = map(det_head, Burrow^rooms),
    LastLine = map(det_tail, Burrow^rooms),
    MiddleLines = [
      [desert, desert],
      [copper, bronze],
      [bronze, amber],
      [amber, copper]
    ],
    NewRooms = det_zip_with(cons, FirstLine, det_zip_with(append, MiddleLines, LastLine))
  else
    throw("undefined")
  ).

:- pred solve(burrow::in, io::di, io::uo) is det.
solve(Burrow, !IO) :-
  io.print_line("Solving for " ++ string(Burrow) ++ ":", !IO),
  % Part 1
  (if find_min_energy_moves(Burrow, Moves, EnergySpent) then
    io.format("Part 1: %i\r\n", [i(EnergySpent)], !IO),
    io.print_line(join_list("\r\n", map(pipe2(swap, string), reverse(Moves))), !IO),
    io.nl(!IO)
  else
    true
  ),

  % Part 2
  ExtendedBurrow = extend_burrow(Burrow),
  (if find_min_energy_moves(ExtendedBurrow, MovesP2, EnergySpentP2) then
    io.format("Part 2: %i\r\n", [i(EnergySpentP2)], !IO),
    io.print_line(join_list("\r\n", map(pipe2(swap, string), reverse(MovesP2))), !IO),
    io.nl(!IO)
  else
    true
  ),
  io.nl(!IO).

main(!IO) :-
  Inputs = [
    burrow(
      [[bronze, amber], [copper, desert], [bronze, copper], [desert, amber]],
      2,
      map.init
    ),
    burrow(
      [[desert, copper], [copper, desert], [amber, amber], [bronze, bronze]],
      2,
      map.init
    )
  ],
  foldl(solve, Inputs, !IO).