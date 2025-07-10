-module(play).
-compile(export_all).

process (F) ->
    Pid = spawn(?MODULE, F  ) ,
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