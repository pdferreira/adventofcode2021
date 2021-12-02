:- module utils.

:- interface.
:- import_module string, list, io.
:- pred read_lines(list(string)::out, io::di, io::uo) is det.
:- pred read_lines(string::in, list(string)::out, io::di, io::uo) is det.

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