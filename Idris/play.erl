-module(play).
-compile(export_all).


process_function (Fun, P) -> 
    receive 
        M -> io:format("process received: ~p~n", [M]), 
             P ! Fun(M)
    end.

process_function_stream (Fun, P) -> 
    receive 
        stop -> P ! stop;
        M -> io:format("process received: ~p~n", [M]), 
             P ! Fun(M),
             process_function_stream(Fun, P)
    end.

drain(P) ->
    receive 
        M -> io:format("drain received: ~p~n", [M]), 
             P ! M
    end.

drain_stream(P) ->
    receive 
        stop -> io:format("drain received Stop!: ~n", []),
                P ! stop;
        M -> io:format("drain received: ~p~n", [M]), 
             P ! M,
             drain_stream(P)
    end.


% process : (f : a -> b) -> Process a b
process (F) ->
    Sus = spawn(play, drain, [self()]),
    Pid = spawn(play, process_function, [F, Sus]) ,
    {Pid, Sus}.

% process_stream : (f : [a] -> b) -> Process [a] b
process_stream (F) ->
    Sus = spawn(play, drain_stream, [self()]),
    Pid = spawn(play, process_function_stream, [F, Sus]) ,
    {Pid, Sus}.

% <#> : Process a b -> a -> Sus b
app ({P, S}, M) ->
    P ! M . 

% <#> : Process [a] b -> a -> Sus b
app_stream ({P, S}, []) ->P ! stop;
app_stream ({P, S}, [X | Xs]) ->
    P ! X ,
    app_stream ({P,S}, Xs). 

% sync : Sus a -> a 
sync (_) ->
    receive 
        M -> M
    end.

%sync_stream : Sus [a] -> [a]
sync_stream (X) ->
    receive
        stop -> [] ;
        M -> [M | sync_stream(X) ]
    end.


% ------------------

parMap1 (F,[]) -> [];
parMap1 (F,[X|Xs]) -> 
    [app (process(F), X) | parMap1(F,Xs)].

parMap(F,[]) -> [];
parMap(F,Xs) ->
    lists:map (fun(Y) -> sync(Y) end, (parMap1(F, Xs))).

% processN : (f : a -> b) -> (n : Nat) -> Vect n (Process a b)


% sync2 : Sus (Vect n b) -> Maybe b 

% <$$> : ([a] -> [b]) -> ([b] -> [c]) -> Process [a] [c]
comp (F2, F1) ->
    Sus = spawn(play, drain_stream, [self()]),
    Pid1 = spawn(play, process_function_stream, [F2, Sus]),
    Pid2 = spawn(play, process_function_stream, [F1, Pid1]) ,
    {Pid2, Sus}.

% ---------------------------------

pipe2 (F1, F2, Inputs) ->
   sync_stream(app_stream(comp(F2, F1), Inputs)).

%    appStream (process(F1), Inputs),

fib(N) when N =< 1 -> 
    N;
fib(N) -> fib (N-1) + fib (N-2).

fibL([X|R]) when X =< 1 ->
        X;
fibL([X|R]) ->
    fibL([X-1]) + fibL([X-2]) + fibL([X-3]) + fibL([X-4]).
      
testFib(N) ->
   fibL([N]),
   fibL([N]),  
   fibL([N]),
   fibL([N]).