:- module day16.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, char, exception.
:- import_module utils.

:- type bit == int.
:- type packet ---> 
  literal(lit_version :: int, value :: int) ;
  operator(op_version :: int, type_id :: int, sub_packets :: list(packet)).

:- inst packet for packet/0 --->
  literal(ground, ground) ;
  operator(ground, ground, non_empty_list).

:- pred hex_to_bit_list(char::in, list(bit)::out) is semidet.
hex_to_bit_list('0', [0, 0, 0, 0]).
hex_to_bit_list('1', [0, 0, 0, 1]).
hex_to_bit_list('2', [0, 0, 1, 0]).
hex_to_bit_list('3', [0, 0, 1, 1]).
hex_to_bit_list('4', [0, 1, 0, 0]).
hex_to_bit_list('5', [0, 1, 0, 1]).
hex_to_bit_list('6', [0, 1, 1, 0]).
hex_to_bit_list('7', [0, 1, 1, 1]).
hex_to_bit_list('8', [1, 0, 0, 0]).
hex_to_bit_list('9', [1, 0, 0, 1]).
hex_to_bit_list('A', [1, 0, 1, 0]).
hex_to_bit_list('B', [1, 0, 1, 1]).
hex_to_bit_list('C', [1, 1, 0, 0]).
hex_to_bit_list('D', [1, 1, 0, 1]).
hex_to_bit_list('E', [1, 1, 1, 0]).
hex_to_bit_list('F', [1, 1, 1, 1]).

:- pred read_bit_list(string::in, list(bit)::out) is semidet.
read_bit_list(Str, Bits) :-
  map(hex_to_bit_list, to_char_list(Str), BitLists),
  condense(BitLists, Bits).

:- func bit_list_to_string(list(bit)) = string.
bit_list_to_string([]) = "".
bit_list_to_string([B|Bs]) = string(B) ++ bit_list_to_string(Bs).

:- func bit_list_to_int(list(bit)) = int.
bit_list_to_int(Bs) = det_base_string_to_int(2, bit_list_to_string(Bs)).

:- pred take_n_bits(int::in, list(bit)::out, list(bit)::in, list(bit)::out) is semidet.
take_n_bits(N, Bits) -->
  (if { N = 0 } then
    { Bits = [] }
  else
    [B],
    take_n_bits(N - 1, Bs),
    { Bits = [B|Bs] }
  ).

:- pred parse_packet(packet::out(packet), list(bit)::in, list(bit)::out) is semidet.
parse_packet(PacketOut) -->
  take_n_bits(3, VersionBits),
  { Version = bit_list_to_int(VersionBits) },
  take_n_bits(3, TypeIdBits),
  { TypeId = bit_list_to_int(TypeIdBits) },
  
  (if { TypeId = 4 } then % it's a literal
    parse_value(ValueBits),
    { PacketOut = literal(Version, bit_list_to_int(ValueBits)) }
  else
    [LengthIdBit],
    (if { LengthIdBit = 0 } then
      take_n_bits(15, LengthBits),
      { TotalSubPacketBits = bit_list_to_int(LengthBits) },
      parse_packets_until_bit_limit(TotalSubPacketBits, SubPackets @ [_|_])
    else
      take_n_bits(11, NumSubPacketBits),
      { TotalSubPackets = bit_list_to_int(NumSubPacketBits) },
      parse_n_packets(TotalSubPackets, SubPackets @ [_|_])
    ),
    { PacketOut = operator(Version, TypeId, SubPackets) }
  ).

:- pred parse_value(list(bit)::out, list(bit)::in, list(bit)::out) is semidet.
parse_value(ValueBits) -->
  [ContinueBit],
  take_n_bits(4, CurrValueBits),
  (if { ContinueBit = 0 } then
    { ValueBits = CurrValueBits }
  else
    parse_value(NextValueBits),
    { append(CurrValueBits, NextValueBits, ValueBits) }
  ).

:- pred parse_packets_until_bit_limit(int::in, list(packet)::out, list(bit)::in, list(bit)::out) is semidet.
parse_packets_until_bit_limit(MaxBits, [P|Ps]) -->
  =(CurrBitsBefore),
  parse_packet(P),
  =(CurrBitsAfter),
  { ConsumedBits = length(CurrBitsBefore) - length(CurrBitsAfter) },
  { ConsumedBits =< MaxBits },
  (if parse_packets_until_bit_limit(MaxBits - ConsumedBits, NextPs) then
    { Ps = NextPs }
  else
    { Ps = [] }
  ).

:- pred parse_n_packets(int::in, list(packet)::out, list(bit)::in, list(bit)::out) is semidet.
parse_n_packets(N, Ps) -->
  (if { N = 0 } then
    { Ps = [] }
  else
    { Ps = [P|NextPs] },
    parse_packet(P),
    parse_n_packets(N - 1, NextPs)
  ).

:- func sum_versions(packet) = int is det.
sum_versions(literal(Version, _)) = Version.
sum_versions(operator(Version, _, Ps)) = Version + sum(map(sum_versions, Ps)).

:- func eval(packet) = int.
% :- mode eval(in(packet)) = out is det.
eval(literal(_, Value)) = Value.
eval(operator(_, 0, Ps)) = sum(map(eval, Ps)).
eval(operator(_, 1, Ps)) = product(map(eval, Ps)).
eval(operator(_, 2, Ps)) = min(map(eval, Ps)).
eval(operator(_, 3, Ps)) = max(map(eval, Ps)).
eval(operator(_, 5, [P1, P2])) = (if eval(P1) > eval(P2) then 1 else 0).
eval(operator(_, 6, [P1, P2])) = (if eval(P1) < eval(P2) then 1 else 0).
eval(operator(_, 7, [P1, P2])) = (if eval(P1) = eval(P2) then 1 else 0).
eval(operator(_, _, _)) = _ :- throw("unexpected").

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),
  read_lines(FileName, Lines, !IO),
  (if
    [L|_] = Lines,
    read_bit_list(L, Bits),
    parse_packet(Packet, Bits, _)
  then
    %io.print_line(bit_list_to_string(Bits), !IO),
    
    % Part 1
    io.print_line(Packet, !IO),
    VersionSum = sum_versions(Packet),
    io.print_line("Part 1: " ++ string(VersionSum), !IO),

    % Part 2
    Result = eval(Packet),
    io.print_line("Part 2: " ++ string(Result), !IO)
  else
    true
  ),
  io.nl(!IO).

main(!IO) :-
  Inputs = map(func(Name) = "inputs/" ++ $module ++ "_" ++ Name, [
    "example",
    "example2",
    "example3",
    "example4",
    "example5",
    "example6",
    "example7",
    "input"
  ]),
  foldl(solve, Inputs, !IO).