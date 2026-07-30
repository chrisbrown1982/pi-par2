%% bench_seq.erl -- canonical SEQUENTIAL baselines for the Parallel-Types vs
%% Elysium comparison. Kept deliberately separate from the parallel/farm code
%% so one Ts per benchmark can be used for BOTH speedup computations.
%%
%% The implementations are transcribed to match, line-for-line, the sequential
%% code already present in both codebases:
%%   SumEuler : sumEuler.erl (Elysium) == parSumEuler2.erl (Parallel Types)
%%   MatMul   : parMatMul.erl multiply/2 (both) -- Elysium lacks a seq *driver*,
%%              so this supplies it
%%   CPI      : parCpi.erl cpi/1 (Parallel Types) -- Elysium has no CPI at all,
%%              so this is the canonical reference
%%
%% Timing uses timer:tc (microseconds), so there is no dependency on sk_profile
%% or on either repo's runtime. Run on the SAME machine as the parallel runs:
%%   erl -noinput -eval "bench_seq:run(sumeuler,40000,10), init:stop()."
%%   erl -noinput -eval "bench_seq:run(matmul,4000,10),   init:stop()."
%%   erl -noinput -eval "bench_seq:run(cpi,1000000000,10), init:stop()."

-module(bench_seq).
-export([run/3, sumeuler/1, matmul/1, cpi/1]).

%% ---- SumEuler (identical in both codebases) ----
gcd(A, 0) -> A;
gcd(A, B) -> gcd(B, A rem B).

rel_prime(X, Y) -> gcd(X, Y) =:= 1.

mklist(N) -> lists:seq(1, N).

euler(N) -> length(lists:filter(fun(X) -> rel_prime(N, X) end, mklist(N))).

sumeuler(N) -> lists:sum(lists:map(fun euler/1, mklist(N))).

%% ---- Matrix multiplication (matches parMatMul.erl multiply/2 in both) ----
transpose([[] | _]) -> [];
transpose(B) ->
    [lists:map(fun erlang:hd/1, B) | transpose(lists:map(fun erlang:tl/1, B))].

dot(A, B) -> lists:foldl(fun({X, Y}, S) -> X * Y + S end, 0, lists:zip(A, B)).

row_by_cols(_Row, []) -> [];
row_by_cols(Row, [C | Cs]) -> [dot(Row, C) | row_by_cols(Row, Cs)].

mm_internal([], _B) -> [];
mm_internal([R | Rs], B) -> [row_by_cols(R, B) | mm_internal(Rs, B)].

%% Same matrices the farm benchmark builds: A = B = duplicate(Size, 1..Size);
%% the farm multiplies each row of A against the pre-transposed B, so the
%% sequential reference does the same.
matmul(Size) ->
    A = lists:duplicate(Size, lists:seq(1, Size)),
    Bt = transpose(lists:duplicate(Size, lists:seq(1, Size))),
    mm_internal(A, Bt).

%% ---- Computational pi (matches parCpi.erl cpi/1) ----
f(X) -> 4 / (1 + X * X).
index2(I, N) -> (I - 0.5) / N.

cpi(N) ->
    lists:foldr(fun erlang:'+'/2, 0,
                lists:map(fun(I) -> f(index2(I, N)) end, lists:seq(1, N)))
      / N.

%% ---- timing driver (microseconds -> seconds, mean over Reps) ----
run(Which, Arg, Reps) ->
    F = case Which of
            sumeuler -> fun() -> sumeuler(Arg) end;
            matmul   -> fun() -> matmul(Arg) end;
            cpi      -> fun() -> cpi(Arg) end
        end,
    Times = [begin {T, _} = timer:tc(F), T end || _ <- lists:seq(1, Reps)],
    Mean = lists:sum(Times) / length(Times) / 1.0e6,
    io:format("~p ~p: mean ~.4f s over ~p reps (us: ~p)~n",
              [Which, Arg, Mean, Reps, Times]).
