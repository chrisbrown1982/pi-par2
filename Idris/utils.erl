-module(utils).
-compile(export_all).

fst(A) -> A. % element(1, A).

snd(A) -> A. % element(2, A).

fst2 (A) -> element(1, A).

snd2 (A) -> element(2, A).

n_length_chunks([],_) -> [];
n_length_chunks(List,Len) when Len > length(List) ->
    [List];
n_length_chunks(List,Len) ->
    {Head,Tail} = lists:split(Len,List),
    [Head | n_length_chunks(Tail,Len)].

minus(A,B) -> A - B.

divide(L, N) ->
    divide(L, N, []).
divide([], _, Acc) ->
    lists:reverse(Acc);
divide(L, N, Acc) when length(L) < N ->
    lists:reverse([L|Acc]);
divide(L, N, Acc) ->
    {H,T} = lists:split(N, L),
    divide(T, N, [H|Acc]).

drop(_, []) ->
     [];
drop(0, Collection) ->
    Collection;
drop(Number, [_H | T]) ->
    drop(Number - 1, T).

takeEach(N, []) -> [];
takeEach(N, [X|Xs]) ->
    [ X | takeEach(N, drop((N-1), Xs))].

unshuffle(N, Xs) -> 
    [ takeEach(N, (drop(I, Xs))) || I <- lists:seq(0, (N-1))].

s (N) -> N + 1. 

mkMsg ([] )  ->
        [mend ];
mkMsg ( ([X|Xs]) )  ->
        [{msg ,X } | ?MODULE:mkMsg( Xs  ) ].

