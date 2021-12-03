:- module day03.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module string, list, int, char.
:- import_module utils.

:- type bit == int.
:- type binary_number == list(bit).
:- type index == int.

:- pred read_bitstring(string::in, binary_number::out) is semidet.
read_bitstring(Str, Bs) :-
  Cs = to_char_list(Str),
  map(binary_digit_to_int, Cs, Bs).

:- pred transpose(list(list(T))::in, list(list(T))::out) is det.
transpose([], []).
transpose([Xs], Zs) :- chunk(Xs, 1, Zs).
transpose([X|Xs @ [_|_]], Zs) :-
  transpose(Xs, Ys),
  map_corresponding(cons, X, Ys, Zs).

:- func count_ones(list(binary_number)) = list(int).
count_ones(BNs) = Os :-
  transpose(BNs, TBNs),
  map(sum, TBNs) = Os.

:- func binary_number_to_int(binary_number) = int.
binary_number_to_int(Digits) = det_base_string_to_int(2, append_list(map(string, Digits))).

:- func count_if(pred(T), list(T)) = int.
:- mode count_if(pred(in) is semidet, in) = out is det.
count_if(_, []) = 0.
count_if(P, [X|Xs]) = (if P(X) then 1 else 0) + count_if(P, Xs). 

:- func filter_by_index(list(list(T)), index, T) = list(list(T)).
filter_by_index(XXs, Idx, V) = filter((pred(Xs::in) is semidet :- member_index0(V, Xs, Idx)), XXs).

:- func rating(pred(int, int), list(binary_number), index) = list(binary_number).
:- mode rating(pred(in, in) is semidet, in, in) = out is semidet.
rating(_, [BN], _) = [BN].
rating(Comparer, BNs @ [_,_|_], Idx) = ResultBNs :-
  FilteredBNs = filter_by_index(BNs, Idx, 1),
  TotalOnes = length(FilteredBNs),
  TotalZeros = length(BNs) - TotalOnes, 
  (if Comparer(TotalZeros, TotalOnes) then
    ResultBNs = rating(Comparer, FilteredBNs, Idx + 1)
  else
    ResultBNs = rating(Comparer, filter_by_index(BNs, Idx, 0), Idx + 1)
  ).

:- func oxigen_generator_rating(list(binary_number)) = list(binary_number) is semidet.
oxigen_generator_rating(BNs) = rating(Comparer, BNs, 0) :-
  Comparer = (pred(TotalZeros::in, TotalOnes::in) is semidet :- TotalZeros =< TotalOnes).


:- func co2_scrubber_rating(list(binary_number)) = list(binary_number) is semidet.
co2_scrubber_rating(BNs) = rating(Comparer, BNs, 0) :-
  Comparer = (pred(TotalZeros::in, TotalOnes::in) is semidet :- TotalZeros > TotalOnes).

:- pred solve(string::in, io::di, io::uo) is det.
solve(FileName, !IO) :-
  io.print_line("Solving for " ++ FileName ++ ":", !IO),

  read_lines(FileName, Lines, !IO),
  (if map(read_bitstring, Lines, BNs) then
    Ones = count_ones(BNs),
    TotalBNs = length(BNs),

    GammaDigits = map((func(Count) = (if Count >= TotalBNs / 2 then 1 else 0)), Ones),
    GammaRate = binary_number_to_int(GammaDigits),
    
    EpsilonDigits = map(minus(1), GammaDigits),
    EpsilonRate = binary_number_to_int(EpsilonDigits),
    io.print_line("Part 1: " ++ string(GammaRate * EpsilonRate), !IO),

    (if 
      [OGRatingDigits] = oxigen_generator_rating(BNs),
      [CSRatingDigits] = co2_scrubber_rating(BNs) 
    then
      OGRating = binary_number_to_int(OGRatingDigits),
      CSRating = binary_number_to_int(CSRatingDigits),
      io.print_line("Part 2: " ++ string(OGRating * CSRating), !IO)
    else
      io.print_line("Not able to find Oxigen Generator Rating", !IO)
    )
  else
    io.print_line("Failed to parse input", !IO)
  ).

main(!IO) :-
  solve("inputs/day03_example", !IO),
  io.nl(!IO),
  solve("inputs/day03_part1", !IO).
