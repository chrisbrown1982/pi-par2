-module(play2).
-compile(export_all).


drain_stream2( []) -> 
  receive 
    {sus_data, M} -> 
        % io:format("drain2 received ~p ~n", [M]),
        drain_stream2( [M]);
    {release, Pid} ->
        % io:format("drain2 releasing empty ~n", []),
        Pid ! [],
        drain_stream2([])
  end;
drain_stream2([R | Results]) -> 
  receive 
    {sus_data, M} -> 
        % io:format("drain2 received ~p ~n", [M]),
        drain_stream2( [R | Results] ++ [M]);
    {release, Pid} ->
        % io:format("drain2 releasing ~p ~n", [R]),
        Pid ! R,
        drain_stream2(Results)
  end.


drain_stream() -> 
  receive 
    {sus_data, M} -> 
        % io:format("drain received ~p ~n", [M]),
        drain_stream2( [M])
  end.


process_function_stream(Fun, Sus) ->
    receive
        stop -> stop; 
        {proc_data, M} ->
            % io:format("process_function_stream: ~p~n", [M]),
            Sus ! {sus_data, Fun(M)},
            process_function_stream(Fun, Sus)
    end.


% process : (f : [a] -> [b]) -> Process [a] [b]
process(F) ->
    Sus = spawn(play2, drain_stream, []),
    Pid = spawn(play2, process_function_stream, [F, Sus]) ,
    {Pid, Sus}.


distributor([Pid | Pids]) ->
    receive 
        M -> % io:format("distributor received: ~p~n", [M]), 
             Pid ! {proc_data, M},
             distributor( lists:append(Pids, [Pid]))
    end.

processN2 (0, F, Sus) -> [];
processN2 (N, F, Sus) ->
    % io:format("creating farm process: ~n", []),
    Pid = spawn(play2, process_function_stream, [ F, Sus]),
    [Pid | processN2((N-1), F, Sus)].

% processN : (n : Nat) -> (f : [a] -> [b]) -> Processes [a] [b]
processN(N, F) -> 
    Sus = spawn(play2, drain_stream, []),
    Pids = processN2(N, F, Sus),
    Distr = spawn(play2, distributor, [Pids]),
    {Pids, Sus, Distr}.


% app_stream : Process [a] [b] -> a -> Sus b 
% <#>
app_stream({Pid, Sus}, X) ->
    Pid ! {proc_data, X},
    Sus. 

% sync_stream : Sus b -> b 
sync_stream(Sus) ->
    Sus ! {release, self()},
    receive 
        M ->  % io:format("sync_stream releasing: ~p ~n", [M]),
              M
    end. 

% sync_stream2 : Sus [b] -> [b] 
% needs a vector with a size
sync_stream2(Sus, 0) -> [];
sync_stream2(Sus, N) ->
    Sus ! {release, self()},
    receive 
        stop -> [];
        [] -> sync_stream2(Sus, N);
        M ->  %  io:format("sync_stream releasing: ~p ~n", [M]),
              [M | sync_stream2(Sus, N-1)]
    end. 


% distribute : Processes [a] [b] -> a -> Sus [b]
distribute({Pids, Sus, Distr}, X) ->
    Distr ! X.

% distributeL : Processes [a] [b] -> [a] -> Sus [b] 
distributeL ({Pids, Sus, Distr}, []) ->
    Sus;
distributeL ({Pids, Sus, Distr}, [X | Xs]) ->
    Distr ! X,
    distributeL ({Pids, Sus, Distr}, Xs).

taskFarm (F, Nw, Inputs) ->
    Workers = processN(Nw, F),
    sync_stream2(distributeL(Workers, Inputs), length(Inputs)).

% connect : Processes [a] [b] -> Sus [a] -> Sus [b] 
connect({Pids, Sus, Distr}, Sus2, 0) -> Sus;
connect({Pids, Sus, Distr}, Sus2, N) ->
    R = sync_stream2(Sus2,1),
    % io:format ("Sending ~p to Stage 2 ~n", [R]),
    distributeL({Pids, Sus, Distr}, R),
    connect({Pids, Sus, Distr}, Sus2, N-1).

nest (F1, Nw1, F2, Nw2, Inputs) ->
    Farm1 = processN(Nw1, F1),

    SusF1 = distributeL(Farm1, Inputs),

    Farm2 = processN(Nw2, F2),

    SusF2 = connect(Farm2, SusF1, length(Inputs)),

    sync_stream2(SusF2, length(Inputs)).


parMap(F, []) -> [];
parMap(F, [X|Xs]) -> 
    [ app_stream(process(F), X) | parMap(F, Xs)].

fib(0) -> 0;
fib(1) -> 1;
fib(N) -> fib(N-1) + fib(N-2).

fibDC([0, T]) -> 0;
fibDC([1, T]) -> 1;
fibDC([N, T]) when N < T -> fib(N);
fibDC([N, T]) when N >= T -> 
    S1 = app_stream(process(fun fibDC/1), [N-1, T]),
    S2 = app_stream(process(fun fibDC/1), [N-2, T]),
    sync_stream(S1) + sync_stream(S2). 
