%% Minimal self-contained sk_profile:benchmark/3 shim.
%% Same API and output proplist as skel's sk_profile (min/max/med/mean/std_dev
%% in microseconds via timer:tc), but with no skel.hrl / skel dependency, so the
%% comparison directory is self-contained. Output format matches the existing
%% farm_*.txt files exactly.
-module(sk_profile).
-export([benchmark/3]).

benchmark(Fun, Args, N) when N > 0 ->
    Times = [begin {T, _} = timer:tc(Fun, Args), T end || _ <- lists:seq(1, N)],
    Sorted = lists:sort(Times),
    Mean = lists:sum(Times) / N,
    Var = case N of
              1 -> 0.0;
              _ -> lists:sum([(T - Mean) * (T - Mean) || T <- Times]) / (N - 1)
          end,
    [{n, N},
     {min, hd(Sorted)},
     {max, lists:last(Sorted)},
     {med, lists:nth((N + 1) div 2, Sorted)},
     {mean, Mean},
     {std_dev, math:sqrt(Var)}].
