:- module day24.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, char, map, solutions, int64, pair, exception, bool.
:- import_module utils.

:- type register == char.
:- type alu_state == map(register, int).
:- type instr_arg ---> register(register) ; number(int).
:- type instr --->
  inp(register) ;
  add(register, instr_arg) ;
  mul(register, instr_arg) ;
  div(register, instr_arg) ;
  mod(register, instr_arg) ;
  eql(register, instr_arg).
:- type program == list(instr).

:- pred parse_instr(string::in, instr::out) is semidet.
parse_instr(Line, Instr) :-
  [InstrName, RegNameStr|Args] = words(Line),
  [RegName] = to_char_list(RegNameStr),
  (if InstrName = "inp" then
    Instr = inp(RegName)
  else
    Args = [RegOrNum],
    (if to_int(RegOrNum, Num) then
      InstrArg = number(Num)
    else 
      [OtherRegName] = to_char_list(RegOrNum),
      InstrArg = register(OtherRegName)
    ),
    (
      InstrName = "add", Instr = add(RegName, InstrArg) ;
      InstrName = "mul", Instr = mul(RegName, InstrArg) ;
      InstrName = "div", Instr = div(RegName, InstrArg) ;
      InstrName = "mod", Instr = mod(RegName, InstrArg) ;
      InstrName = "eql", Instr = eql(RegName, InstrArg) ;
      fail
    )
  ).

:- func get_value(instr_arg, alu_state) = int.
get_value(register(R), Store) = Store^det_elem(R).
get_value(number(N), _) = N.

:- pred alu_run_bin_op(register::in, instr_arg::in, (func(int, int) = int)::in, alu_state::in, alu_state::out) is det.
alu_run_bin_op(R, Arg, OpFn, Store, map.det_update(Store, R, Result)) :-
  LeftV = Store^det_elem(R),
  RightV = get_value(Arg, Store),
  Result = OpFn(LeftV, RightV).

:- pred alu_run(instr::in, list(int)::in, list(int)::out, alu_state::in, alu_state::out) is det.
alu_run(inp(_), [], _, _, _) :- throw("Expected input, found none").
alu_run(inp(R), [I|Is], Is, Store, map.det_update(Store, R, I)).
alu_run(add(R, Arg), !Is, !Store) :- alu_run_bin_op(R, Arg, (func(A, B) = A + B), !Store).
alu_run(mul(R, Arg), !Is, !Store) :- alu_run_bin_op(R, Arg, (*), !Store).
alu_run(div(R, Arg), !Is, !Store) :- alu_run_bin_op(R, Arg, (/), !Store).
alu_run(mod(R, Arg), !Is, !Store) :- alu_run_bin_op(R, Arg, (func(A, B) = A mod B), !Store).
alu_run(eql(R, Arg), !Is, !Store) :- alu_run_bin_op(R, Arg, (func(A, B) = (if A = B then 1 else 0)), !Store).

:- pred alu_run_program(list(int)::in, program::in, alu_state::in, alu_state::out) is det.
alu_run_program(Inputs, Instrs, InStore, OutStore) :-
  foldl2(alu_run, Instrs, Inputs, _, InStore, OutStore).

:- pred alu_run_program(list(int)::in, program::in, alu_state::out) is det.
alu_run_program(Inputs, Instrs, OutStore) :-
  InStore = map.from_corresponding_lists([w, x, y, z], [0, 0, 0, 0]),
  alu_run_program(Inputs, Instrs, InStore, OutStore).

:- pred alu_run_example(string::in, program::in, io::di, io::uo) is det.
alu_run_example(Name, Example, !IO) :-
  io.nl(!IO),
  io.print("Running " ++ Name ++ ": ", !IO),
  read(ReadRes, !IO),
  (if ReadRes = ok(Nums : list(int)) then
    alu_run_program(Nums, Example, Store),
    io.print_line(map_to_string(Store), !IO)
  else
    throw(ReadRes)
  ).

:- pred alu_run_examples(io::di, io::uo) is det.
alu_run_examples(!IO) :-
  Examples = [
    [
      inp(x),
      mul(x, number(-1))
    ],
    [
      inp(z),
      inp(x),
      mul(z, number(3)),
      eql(z, register(x))
    ]
  ],
  alu_run_example("Example1", det_index1(Examples, 1), !IO),
  alu_run_example("Example2", det_index1(Examples, 2), !IO).

:- pred chunk_by_inp_aux(program::in, list(program)::in, list(program)::out) is det.
chunk_by_inp_aux([], ChunksIn, ChunksOut) :- ChunksOut = reverse(map(reverse, ChunksIn)).
chunk_by_inp_aux([Instr|Instrs], ChunksIn, ChunksOut) :-
  (if Instr = inp(_) then
    chunk_by_inp_aux(Instrs, [[Instr]|ChunksIn], ChunksOut)
  else if ChunksIn = [C|Cs] then
    chunk_by_inp_aux(Instrs, [[Instr|C]|Cs], ChunksOut)
  else
    throw("unexpected")
  ).
    
:- func chunk_by_inp(program) = list(program).
chunk_by_inp(Instrs) = Chunks :- chunk_by_inp_aux(Instrs, [], Chunks).

:- pred possible_model_number(int::in, list(int)::out) is nondet.
possible_model_number(NumDigits, PossibleModelNum) :-
  foldl(
    (pred(_::in, Ns::in, [N|Ns]::out) is nondet :- member(N, 1 .. 9)),
    1 .. NumDigits,
    [],
    PossibleModelNumRev
  ),
  PossibleModelNum = reverse(PossibleModelNumRev).

:- pred bruteforce(program::in, list(list(int))::out) is det.
bruteforce(Program, ValidIs) :-
  NumInputs = length(chunk_by_inp(Program)),
  promise_equivalent_solutions [ValidIs] unsorted_aggregate(
    possible_model_number(NumInputs),
    (pred(Is::in, AllValidIs::in, NewAllValidIs::out) is det :- 
      alu_run_program(Is, Program, Store),
      (if Store^det_elem('z') = 0 then
        NewAllValidIs = [Is|AllValidIs]
        % ,trace [io(!IO2)] io.print_line(string(Is) ++ " is valid", !IO2)
      else
        NewAllValidIs = AllValidIs
      )
      ,trace [io(!IO2)] io.print_line(string(Is) ++ " ---> z = " ++ string(Store^det_elem('z')), !IO2)
    ),
    [],
    ValidIs
  ).

% Main solution insight: 
% - the input program has mostly independent chunks per input digit
% - their only dependency on the previous chunk is the z state
% - w, y and x registers are all overridden before use
%
% Looking at raw data from bruteforcing, there are a lot of duplicate z states
% so the idea is to progressively process by chunk, removing duplicate z's along the way
% to avoid repeating searches
%
:- pred chunked_bruteforce_step(pred(int64, int64), program, map(int, int64), map(int, int64)).
:- mode chunked_bruteforce_step(in(pred(in, in) is semidet), in, in, out) is det.
chunked_bruteforce_step(ShouldSavePred, P, PrevSavedInputByZ, NewSavedInputByZ) :-
  % trace [io(!IO)] (
  %   (if remove_smallest(_, ExampleIs, PrevSavedInputByZ, _) then
  %     io.format("Running program chunk %i on %i inputs\r\n", [
  %       i(if count(PrevSavedInputByZ) = 1 then 1 else 1 + length(int64_to_string(ExampleIs))),
  %       i(count(PrevSavedInputByZ) * 9)
  %     ], !IO)
  %   else
  %     true
  %   )
  % ),
  promise_equivalent_solutions [NewSavedInputByZ] unsorted_aggregate(
    % Given all the combinations of previous inputs and digits 1-9
    (pred((Z - (Is - I))::out) is nondet :- 
      member(PrevSavedInputByZ, Z, Is),
      member(I, 1 .. 9)
    ),
    % Run this chunk using each (prev_z, digit) pair as input
    % and build the map that will feed the next phase (either saving Max or Min depending on ShouldSavePred)
    (pred((PrevZ - (PrevIs - NewI))::in, InSavedInputByZ::in, OutSavedInputByZ::out) is det :-
      InStore = map.from_corresponding_lists([w, x, y, z], [0, 0, 0, PrevZ]),
      alu_run_program([NewI], P, InStore, OutStore),
      NewZ = OutStore^det_elem('z'),

      % Arbitrary cut-off on the search space to avoid OOM, knowing z's have to go down eventually
      (if NewZ < 1000000 then 
        NewIs = PrevIs * int64.from_int(10) + int64.from_int(NewI),
        (if search(InSavedInputByZ, NewZ, SavedIs) then
          (if ShouldSavePred(SavedIs, NewIs) then
            det_update(NewZ, NewIs, InSavedInputByZ, OutSavedInputByZ)
          else
            OutSavedInputByZ = InSavedInputByZ
          )
        else
          det_insert(NewZ, NewIs, InSavedInputByZ, OutSavedInputByZ)
        )
      else
        OutSavedInputByZ = InSavedInputByZ
      )
    ),
    map.init,
    NewSavedInputByZ
  ).

:- pred chunked_bruteforce(pred(int64, int64), program, map(int, int64)).
:- mode chunked_bruteforce(in(pred(in, in) is semidet), in, out) is det.
chunked_bruteforce(ShouldSavePred, Program, MaxInputByZ) :-
  ProgramChunks = chunk_by_inp(Program),
  foldl(
    chunked_bruteforce_step(ShouldSavePred),
    ProgramChunks, 
    map.singleton(0, int64.from_int(0)), 
    MaxInputByZ
  ).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    map(parse_instr, Lines, Program)
  then
    % Part 1
    chunked_bruteforce((<), Program, MaxInputByZ),
    (if search(MaxInputByZ, 0, MaxInput) then
      io.print_line("Part 1: " ++ int64_to_string(MaxInput), !IO)
    else
      io.print_line("Max number with z = 0 not found", !IO)
    ),
    io.nl(!IO),
    
    % Part 2
    chunked_bruteforce((>), Program, MinInputByZ),
    (if search(MinInputByZ, 0, MinInput) then
      io.print_line("Part 2: " ++ int64_to_string(MinInput), !IO)
    else
      io.print_line("Min number with z = 0 not found", !IO)
    )
  else
    true
  ),
  io.nl(!IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "input"
  ]),
  foldl(solve, Inputs, !IO).