-module(msort).
-compile(export_all).


fibDC([0, T]) -> 0;
fibDC([1, T]) -> 1;
fibDC([N, T]) when N < T -> fib(N);
fibDC([N, T]) when N >= T ->
    S1 = play2:app_stream(play2:process(fun fibDC/1), [N-1, T]),
    S2 = play2:app_stream(play2:process(fun fibDC/1), [N-2, T]),
    play2:sync_stream(S1) + play2:sync_stream(S2).


sortMerge([], Ylist) -> Ylist;
sortMerge(XList, []) -> XList;
sortMerge([X|Xs], [Y|Ys]) when X <= Y ->
	[X | sortMerge(Xs, [Y|Ys])];
sortMerge([X|Xs], [Y|Ys]) when X >= Y ->
	[Y | sortMerge([X|Xs], Ys]). 


split([], SoFar) -> SoFar;
split([A|As], {Fs, Ss}) ->
	split(As, {Ss, [A|Fs]}).


mergeSort([]) -> [];
mergeSort([X]) -> [X];
mergeSort(Xs) ->
	{Th, Bh} = split(Xs, {[],[]}),
	sortMerge(mergeSort(Th),mergeSort(Bh)).

mergeSortPar([]) -> [];
mergeSortPar([X]) -> [X];
mergeSortPar(Xs) ->
        {Th, Bh} = split(Xs, {[],[]}),
	S1 = play2:app_stream(play2:process(fun mergeSortPar/1), [Th]),
	S2 = play2:app_stream(play2:process(fun mergeSortPar/1), [Bh]),
	sortMerge(play2:sync_stream(S1), play2:sync_stream(S2)).


generate_random_int_list(N,StartVal,Lim) ->
    lists:map(fun (_) -> random:uniform(Lim-StartVal) + StartVal end, lists:seq(1,N)).


runMergeSeq(Size) ->
   List = generate_random_int_list(Size, 0, 10000),
   io:format("fib seq ~p~n", [sk_profile:benchmark(fun ?MODULE:mergeSort/1, [List], 1)]).

runFibDC(Nw, Thres, Size) -> 
   erlang:system_flag(schedulers_online, Nw), 
   List = generate_random_int_list(Size, 0, 10000),
   io:format("Merge Sort ~p~n", [sk_profile:benchmark(fun ?MODULE:mergeSortPar/1, [Size], 1)]),
   io:format("Done with examples on ~p cores.~n--------~n", [Nw]).




