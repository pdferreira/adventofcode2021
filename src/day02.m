:- module day02.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, char.
:- import_module utils.

:- type horiz == int.
:- type depth == int.
:- type aim == int.

:- type position ---> pos(horiz, depth).
:- type position3 ---> pos(horiz, depth, aim).
:- type action ---> forward(int) ; up(int) ; down(int).

:- pred read_action(string::in, action::out) is semidet.
read_action(ActionText, Action) :-
  [Name, ValueText] = words_separator(char.is_whitespace, ActionText),
  string.to_int(ValueText, Value),
  (
    Name = "forward",
    Action = forward(Value)
  ;
    Name = "up",
    Action = up(Value)
  ;
    Name = "down",
    Action = down(Value)
  ).

:- func apply_action(action, position) = position.
apply_action(forward(N), pos(H, D)) = pos(H + N, D).
apply_action(up(N), pos(H, D)) = pos(H, D - N).
apply_action(down(N), pos(H, D)) = pos(H, D + N).

:- func apply_action_with_aim(action, position3) = position3.
apply_action_with_aim(forward(N), pos(H, D, A)) = pos(H + N, D + (A * N), A).
apply_action_with_aim(up(N), pos(H, D, A)) = pos(H, D, A - N).
apply_action_with_aim(down(N), pos(H, D, A)) = pos(H, D, A + N).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),

  read_lines(FileName, Lines, !IO),
  (if map(read_action, Lines, Actions) then
    pos(NewH, NewD) = foldl(apply_action, Actions, pos(0, 0)),
    io.print_line("Part 1: " ++ string(NewH * NewD), !IO),

    pos(NewH2, NewD2, _) = foldl(apply_action_with_aim, Actions, pos(0, 0, 0)),
    io.print_line("Part 2: " ++ string(NewH2 * NewD2), !IO)
  else
    io.print_line("Failed to parse input", !IO)
  ).

main(!IO) :-
  solve("inputs/day02_example", !IO),
  io.nl(!IO),
  solve("inputs/day02_part1", !IO).
