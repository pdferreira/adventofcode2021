:- module day21.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, map, std_util, solutions, exception.
:- import_module utils.

:- type player_game_state ---> player_game_state(position :: int, points :: int).
:- type game_state ---> game_state(players :: list(player_game_state), turn :: int, num_rolls :: int).

:- type with_frequency(T) ---> (state :: T) `with_frequency` (frequency :: int).
:- type dirac_player_state == with_frequency(player_game_state).
:- type dirac_game_state == with_frequency(game_state).

%%% Part 1

:- pred roll_det_dice(int::in, int::out, int::out) is det.
roll_det_dice(NumRolls, NewNumRolls, NextRoll) :- 
  NewNumRolls = NumRolls + 1,
  NextRoll = ((NewNumRolls - 1) mod 100) + 1.

:- pred player_turn(player_game_state::in, player_game_state::out, int::in, int::out).
player_turn(PlayerState, NewPlayerState, !NumRolls) :-
  roll_det_dice(!NumRolls, Roll1),
  roll_det_dice(!NumRolls, Roll2),
  roll_det_dice(!NumRolls, Roll3),
  NewPosition = ((PlayerState^position + Roll1 + Roll2 + Roll3 - 1) mod 10) + 1,
  NewPlayerState = player_game_state(NewPosition, PlayerState^points + NewPosition).

:- pred player_won(player_game_state::in) is semidet.
player_won(PlayerState) :- PlayerState^points >= 1000.

:- func play(game_state) = game_state.
play(Game) = EndGame :-
  Player = det_index1(Game^players, Game^turn),
  player_turn(Player, NewPlayer, Game^num_rolls, NewNumRolls),
  NewGame = game_state(
    det_replace_nth(Game^players, Game^turn, NewPlayer),
    (Game^turn mod length(Game^players)) + 1,
    NewNumRolls
  ),
  (if player_won(NewPlayer) then
    EndGame = NewGame
  else
    EndGame = play(NewGame)
  ).

:- func new_game(list(int)) = game_state.
new_game(PlayerStartPositions) = game_state(Players, 1, 0) :-
  Players = map(func(Pos) = player_game_state(Pos, 0), PlayerStartPositions).

%%% Part 2

:- pred roll_dirac_dice(int::out) is multi.
roll_dirac_dice(1).
roll_dirac_dice(2).
roll_dirac_dice(3).

:- pred roll_dirac_position_delta(int::out) is multi. 
roll_dirac_position_delta(Delta) :-
  roll_dirac_dice(Roll1),
  roll_dirac_dice(Roll2),
  roll_dirac_dice(Roll3),
  Delta = (Roll1 + Roll2 + Roll3) mod 10.

% 27 different roll combinations, but only 7 unique, so we only need
% to explore one universe template as long as we account for its frequency
:- pragma memo(roll_dirac_position_delta_freq/2).
:- pred roll_dirac_position_delta_freq(int::out, int::out) is multi.
roll_dirac_position_delta_freq(Delta, Freq) :-
  promise_equivalent_solutions [PossibleDeltas] unsorted_solutions(roll_dirac_position_delta, PossibleDeltas),
  frequency(PossibleDeltas, DeltaFreq),
  (if member(D, keys(DeltaFreq)) then
    Delta = D,
    Freq = det_elem(Delta, DeltaFreq)
  else
    throw("unexpected")
  ).

:- pred dirac_player_turn(dirac_player_state::in, dirac_player_state::out) is multi.
dirac_player_turn(PlayerState `with_frequency` PlayerStateFreq, NewPlayerState `with_frequency` NewStateFreq) :-
  roll_dirac_position_delta_freq(Delta, DeltaFreq),
  NewPosition = ((PlayerState^position + Delta - 1) mod 10) + 1,
  NewPlayerState = player_game_state(NewPosition, PlayerState^points + NewPosition),
  % The end-to-end frequency builds on the frequency of the "parent" universe
  % That way we keep piling up frequencies, even though we are only simulating one unique copy
  NewStateFreq = PlayerStateFreq * DeltaFreq.

:- pred dirac_player_won(dirac_player_state::in) is semidet.
dirac_player_won(PlayerState `with_frequency` _) :- PlayerState^points >= 21.

:- pred dirac_play_aux(dirac_game_state::in, list(int)::in, list(int)::out) is det.
dirac_play_aux(Game `with_frequency` Freq, !PlayerWins) :-
  % First simulate the current player turn
  Player = det_index1(Game^players, Game^turn),
  promise_equivalent_solutions [PossibleNewPlayers] unsorted_solutions(
    dirac_player_turn(Player `with_frequency` Freq),
    PossibleNewPlayers
  ),
  
  % Then split the universes with wins and the ones with losses
  filter(dirac_player_won, PossibleNewPlayers, NewWinsForPlayer, NoWinsForPlayer),

  % The wins get added
  NewWinsTotal = sum(map(func(NewWin) = NewWin^frequency, NewWinsForPlayer)),
  !:PlayerWins = det_replace_nth(!.PlayerWins, Game^turn, det_index1(!.PlayerWins, Game^turn) + NewWinsTotal), 

  % The losses will generate new game states where the turn is of the next player
  NextTurn = (Game^turn mod length(Game^players)) + 1,
  NewGames = map(
    (func(NoWin) = NoWinState `with_frequency` NoWin^frequency :-
      NoWinState = game_state(
        det_replace_nth(Game^players, Game^turn, NoWin^state),
        NextTurn,
        0 % num rolls is irrelevant for dirac version 
      )
    ),
    NoWinsForPlayer
  ),
  foldl(dirac_play_aux, NewGames, !PlayerWins).

:- func dirac_play(game_state) = list(int).
dirac_play(InitialGame) = NumWonGamesByPlayer :-
  duplicate(length(InitialGame^players), 0, InitialWonGames),
  dirac_play_aux(InitialGame `with_frequency` 1, InitialWonGames, NumWonGamesByPlayer).

:- pred solve(int::in, int::in, io::di, io::uo) is det.
solve(Player1Start, Player2Start, !IO) :-
  io.format("Solving for player 1 starting at %i and player 2 starting at %i\r\n", [i(Player1Start), i(Player2Start)], !IO),
  
  % Part 1
  EndGameP1 = play(new_game([Player1Start, Player2Start])),
  (if find_first_match(isnt(player_won), EndGameP1^players, LosingPlayer) then
    io.format("Part 1: %i\r\n", [i(LosingPlayer^points * EndGameP1^num_rolls)], !IO)
  else
    true
  ),

  % Part 2
  NumWonGamesByPlayer = dirac_play(new_game([Player1Start, Player2Start])),
  (if 
    MaxGamesWonByPlayer = max(NumWonGamesByPlayer)
  then
    % io.print_line(NumWonGamesByPlayer, !IO),
    io.format("Part 2: %i\r\n", [i(MaxGamesWonByPlayer)], !IO)
  else
    true
  ),

  io.nl(!IO).

main(!IO) :-
  solve(4, 8, !IO),
  solve(9, 10, !IO).