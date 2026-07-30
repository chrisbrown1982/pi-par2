%% parCpi.erl -- Elysium task-farm CPI, for the Parallel-Types comparison.
%% Elysium has no CPI benchmark, so this supplies one in the same idiom as
%% parMatMul.erl / parSumEuler2.erl (a play2:taskFarm run + sk_profile).
%%
%% CPI approximates pi = (1/N) * sum_{i=1..N} f((i-0.5)/N), f(x)=4/(1+x^2).
%%
%% Unlike SumEuler/MatMul, the natural per-element task here is a SINGLE float
%% op, so an element-wise farm over [1..N] would mean N messages and an
%% N-element input list -- infeasible at N=1e9. So we present two encodings:
%%
%%   farmCpi/2       -- MATERIALISED sub-list per worker. This mirrors the
%%                      Parallel-Types CPI (which chunks a pre-built Vect), so
%%                      it is the LIKE-FOR-LIKE comparison for R2-W2: same
%%                      strategy (materialise + one chunk per worker), same
%%                      runtime. Expected result: PARITY with PT-dynamic (both
%%                      hit the same data-movement / Amdahl ceiling).
%%
%%   farmCpiStream/2 -- STREAMING: each worker gets only its {Lo,Hi} bounds and
%%                      generates indices on the fly (no materialised range).
%%                      This is the optimisation the paper flags as future work
%%                      ("stream instead of materialise whole Vects"); include
%%                      it only as a bonus, NOT as the head-to-head, since PT
%%                      does not (yet) do this.
%%
%% RUNTIME NOTE: this needs a play2.erl whose `distributor` sends each input
%% element whole (`Pid ! {proc_data, M}`) round-robin -- the version the
%% existing farm_*.txt data was produced with (identical to the Parallel-Types
%% play2.erl). The play2.erl currently sitting in this Idris/ dir has a
%% DIVERGENT distributor (`distributorS` iterates each element), which breaks
%% chunk-style farming and would in fact crash the SumEuler/MatMul farms too --
%% so it is NOT the runtime behind farm_*.txt. Use the simple-distributor play2.
%%
%% Run (same machine as the PT runs, and as bench_seq for the Ts baseline):
%%   erl -noinput -eval "parCpi:run_examples(28,1000000000), init:stop()."

-module(parCpi).
-compile(export_all).

f(X) -> 4 / (1 + X * X).
index2(I, N) -> (I - 0.5) / N.

%% --- chunk 1..N into Nw contiguous ranges ---
%% bounds only (for streaming); materialised sublists (for the like-for-like run)
bounds(N, Nw) ->
    Step = N div Nw,
    [ {(K * Step) + 1, hi(K, Nw, Step, N)} || K <- lists:seq(0, Nw - 1) ].

hi(K, Nw, _Step, N) when K =:= Nw - 1 -> N;
hi(K, _Nw, Step, _N) -> (K + 1) * Step.

%% partial pi-sum over materialised sublist Chunk (worker body, matches PT)
partialList(Chunk, N) ->
    lists:sum(lists:map(fun(I) -> f(index2(I, N)) end, Chunk)).

%% partial pi-sum over range [Lo,Hi] generated on the fly (streaming worker body)
partialRange(Lo, Hi, N) -> partialRange(Lo, Hi, N, 0).
partialRange(Lo, Hi, _N, Acc) when Lo > Hi -> Acc;
partialRange(Lo, Hi, N, Acc) -> partialRange(Lo + 1, Hi, N, Acc + f(index2(Lo, N))).

%% ---- LIKE-FOR-LIKE farm (materialised chunks) : compare this to PT ----
farmCpi(Nw, N) ->
    Chunks = [ lists:seq(Lo, Hi) || {Lo, Hi} <- bounds(N, Nw) ],
    Partials = play2:taskFarm(fun(C) -> partialList(C, N) end, Nw, Chunks),
    lists:sum(Partials) / N.

%% ---- STREAMING farm (bounds only) : bonus, illustrates future-work opt ----
farmCpiStream(Nw, N) ->
    Tasks = bounds(N, Nw),
    Partials = play2:taskFarm(fun({Lo, Hi}) -> partialRange(Lo, Hi, N) end, Nw, Tasks),
    lists:sum(Partials) / N.

%% sequential reference (identical to bench_seq:cpi/1 and PT parCpi:cpi/1)
cpi(N) ->
    lists:sum(lists:map(fun(I) -> f(index2(I, N)) end, lists:seq(1, N))) / N.

run_examples(Nw, N) ->
    erlang:system_flag(schedulers_online, Nw),
    io:format("CPI ~p~n", [sk_profile:benchmark(fun ?MODULE:farmCpi/2, [Nw, N], 1)]),
    io:format("Done with examples on ~p cores.~n--------~n", [Nw]).
