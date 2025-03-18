-module(play).
-compile(export_all).


process_function (Fun, P) -> 
    receive 
        M -> io:format("process received: ~p~n", [M]), 
             P ! Fun(M)
    end.

process_function_stream (T, Fun, P, Na) -> 
    receive 
        stop -> P ! stop;
        M -> io:format("process stream received: ~p ~p ~p~n", [Na, T, M]), 
             P ! Fun(M),
             process_function_stream(T, Fun, P, Na)
    end.

drain(P) ->
    receive 
        M -> io:format("drain received: ~p~n", [M]), 
             P ! M
    end.

drain_stream(P, Na) ->
    receive 
        stop -> io:format("drain_stream received Stop!: ~p ~n", [Na]),
                P ! stop;
        M -> io:format("drain_stream received: ~p ~p ~n", [Na, M]), 
             P ! M,
             drain_stream(P, Na)
    end.

distributor([Pid | Pids], Na) ->
    receive 
        M -> io:format("distributor received: ~p ~p~n", [Na, M]), 
             Pid ! M,
             distributor( lists:append(Pids, [Pid]), Na)
    end.

% process : (f : a -> b) -> Process a b
process (F) ->
    Sus = spawn(play, drain, [self()]),
    Pid = spawn(play, process_function, [F, Sus]) ,
    {Pid, Sus}.

% process_stream : (f : [a] -> b) -> Process [a] b
process_stream (F) ->
    Sus = spawn(play, drain_stream, [self()]),
    Pid = spawn(play, process_function_stream, ["process_stream", F, Sus, "NA"]) ,
    {Pid, Sus}.


processN2 (0, F, Sus, Na) -> [];
processN2 (N, F, Sus, Na) ->
    io:format("creating farm process: ~p ~n", [Na]),
    Pid = spawn(play, process_function_stream, [ "processN", F, Sus, Na]),
    [Pid | processN2((N-1), F, Sus, Na)].

% processN : (n : Nat) -> (f : [a] -> [b]) -> Processes [a] [b]
processN (N, F, Na) -> 
    Drain = spawn(play, drain_stream, [self(), Na]),
    Pids = processN2 (N, F, Drain, Na),
    Distr = spawn(play, distributor, [Pids, Na]),
    {Pids, Distr, Drain}.

% distribute : Processes [a] [b] -> a -> Sus [b]
distribute ({Pids, Distr, Drain}, X) ->
    Distr ! X.

% distributeL : Processes [a] [b] -> [a] -> Sus [b] 
distributeL ({Pids, Distr, Drain}, []) ->
    stop;
distributeL ({Pids, Distr, Drain}, [X | Xs]) ->
    Distr ! X,
    distributeL ({Pids, Distr, Drain}, Xs).

% <#> : Process a b -> a -> Sus b
app ({P, S}, M) ->
    P ! M . 

% <#> : Process [a] b -> a -> Sus b
app_stream ({P, S}, []) ->stop;
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
        M -> io:format("sync_stream : ~20p~n", [M]),
             [M | sync_stream(X) ]
    end.

% sus_app : Processes [a] b -> Sus [a] -> Sus b
sus_app (Ps, X) ->
    receive
        M -> io:format("sus_app recieved and passing on : ~20p~n", [M]),
             distribute(Ps, M),
             sus_app(Ps, X)
    end. 

% ------------------

parMap1 (F,[]) -> [];
parMap1 (F,[X|Xs]) -> 
    [app (process(F), X) | parMap1(F,Xs)].

parMap(F,[]) -> [];
parMap(F,Xs) ->
    lists:map (fun(Y) -> sync(Y) end, (parMap1(F, Xs))).


parMap1_stream (F, []) -> [];
parMap1_stream (F, [X|Xs]) ->
    [app_stream (process_stream(F), X) | parMap1_stream(F, Xs) ].

parMap_stream(F, []) -> [];
parMap_stream(F, Xs) ->
    lists:map (fun(Y) -> sync_stream(Y) end, (parMap1_stream(F, Xs))).

taskFarm (F, NW, Input) -> 
    In2 =   utils:unshuffle(NW, Input),
    parMap_stream(F, In2).



% <$$> : ([a] -> [b]) -> ([b] -> [c]) -> Process [a] [c]
comp (F2, F1) ->
    Sus = spawn(play, drain_stream, [self()]),
    Pid1 = spawn(play, process_function_stream, ["stage2", F2, Sus]),
    Pid2 = spawn(play, process_function_stream, ["stage1", F1, Pid1]) ,
    {Pid2, Sus}.

% ---------------------------------

pipe2 (F1, F2, Inputs) ->
   sync_stream(app_stream(comp(F2, F1), Inputs)).


nest (F1, NW1, F2, NW2, Inputs) ->
    {Farm1Ps, F1Distr, F1Drain} = processN(NW1, F1, "F1"),
    Farm2 = processN(NW2, F2, "F2"),

    sync_stream(sus_app(Farm2, distributeL({Farm1Ps, F1Distr, F1Drain}, Inputs))).


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