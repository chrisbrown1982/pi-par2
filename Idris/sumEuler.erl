-module(sumEuler).

-compile(export_all).

gcd(A, 0) -> A;
gcd(A, B) -> gcd(B, A rem B).


relPrime(X,Y) -> gcd(X, Y) == 1.

mkList(N) -> lists:seq(1,N).


euler(N) -> length( lists:filter(fun(X) -> ?MODULE:relPrime(N,X) end, mkList(N))).


sumEuler(N) -> io:format("~p~n", [lists:sum(lists:map(fun ?MODULE:euler/1,mkList(N)))]).

run_seq(X) ->
	  io:format("SumEuler Seq: ~p~n", [sk_profile:benchmark(fun ?MODULE:sumEuler/1, [X], 1)]),
	  io:format("Done with seq. ~n").
