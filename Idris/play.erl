-module(play).
-compile(export_all).

process_function (Fun, P) -> 
    receive 
        M -> io:format("received: ~p~n", [M]), 
             P ! Fun(M)
    end.


process (F) ->
    Pid = spawn(play, process_function, [F, self()]) ,
    Pid.

app (P, M) ->
    P ! M . 

sync (_) ->
    receive 
        M -> M
    end.

parMap1 (F,[]) -> [];
parMap1 (F,[X|Xs]) -> 
    [app (process(F), X) | parMap1(F,Xs)].

parMap(F,[]) -> [];
parMap(F,Xs) ->
    lists:map (fun(Y) -> sync(Y) end, (parMap1(F, Xs))).

fib([X|R]) when X =< 1 ->
        X;
fib([X|R]) ->
    fib([X-1]) + fib([X-2]) + fib([X-3]) + fib([X-4]).
      
testFib(N) ->
   fib([N]),
   fib([N]),  
   fib([N]),
   fib([N]).