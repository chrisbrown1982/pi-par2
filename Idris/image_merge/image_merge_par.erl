-module(image_merge_par).
-compile(export_all).

farm4 ( InTy , OutTy , Nw , W , Input )  -> 
	Res = 	?MODULE:spawnN( 0  , 4  , InTy  , OutTy  , W  ) ,
	?MODULE:sendN(  ( ?MODULE:convertChans( InTy  , Res  , Input  )  )  ) ,
	Msgs = 	?MODULE:recNChan( OutTy  ,  ( ?MODULE:inChans( Res  )  )  ) ,
	Msgs 
.

iW ( PIn , POut )  -> 
	receive
		X -> case X of
	 ( mend )  -> 
        	
	eos ;
	 ( {msg,M} )  ->
	POut  !  ( {msg , ( list_merge:convertMerge(list_merge:readImage(M  ))) } ) ,

	Y = 	?MODULE:iW( PIn  , POut  ) ,
	{}
end
	end
.


%mergeFarm ( Nw ,X )  -> 
%	Images = mkMsg(list_merge:imageList(X)),
%	Res = 	?MODULE:spawnN( 0  , Nw  , msgt  , msgt  , iW, self()  ) ,
%	?MODULE:roundRobin( msgt  , Images  ,  ( ?MODULE:convertChansRR( Res  )  )  ) ,
%	Msgs = 	?MODULE:roundRobinRec(  ( length( Images  ) -1  )  ,  ( ?MODULE:inChans( Res  )  )  ) ,
%	Msgs 
%.

mergeFarm (Nw, X) -> 
	Images = list_merge:imageList(X),
	play2:taskFarm(fun(I) -> list_merge:convertMerge(list_merge:readImage(I)) end, Nw, Images).

runFarm( Nw, X) -> 
	%erlang:system_flag(schedulers_online, Nw), 
	io:format("Image Merge Farm ~p~n", [sk_profile:benchmark(fun ?MODULE:mergeFarm/2, [Nw, X], 1)]),
	io:format("Done on ~p cores ~n", [Nw]).

%s1 ( PIn , POut )  -> 
%	receive
%		X -> case X of
%	 ( {msg,M} )  ->
 %io:format("S1: ~p~n", [M]),
%$	M2 = list_merge:readImage(M),
%	POut  !  ( {msg , ( M2 ) } ) ,
%	Y = 	?MODULE:s1( PIn  , POut  ) ,
%	{};
%	( mend) -> 
%		POut ! mend, 
%		eos
%end
%	end
%.
%s2 ( PIn , POut )  -> 
%	receive
%		X -> case X of
%	 ( {msg,{T1, T2, T3, T4, T5}} ) -> 
%	%io:format("S2: ~p~n", [M]),
%	M2 = list_merge:convertMerge({T1, T2, T3, T4, T5}),
%	POut  !  ( {msg2 , ( M2 ) } ) ,
%	Y = 	?MODULE:s2( PIn  , POut  ) ,
%	{};
%	( mend ) -> 
%		eos
%end
%	end
%.
%mergePipeFarm ( NW1 , NW2 , X )  -> 
%	erlang:system_flag(schedulers_online, 56),
%	Images = list_merge:imageList(X),
%	ResS2 = 	?MODULE:spawnN( 0  , NW2	  , msgt  , msgt  , s2, self()  ) ,
%	P = spawn(?MODULE,pipeMessages2, [ X, ?MODULE:outChans( ResS2)]) ,
%	ResS1 = 	?MODULE:spawnN( 8  , NW1  , msgt  , msgt  , s1, P  ) ,
%?MODULE:roundRobin( msgt  , Images  ,  ( ?MODULE:convertChansRR( ResS1  )  )  ) ,
%	Msgs = 	?MODULE:roundRobinRec(  X     ,  ( ?MODULE:inChans( ResS2  )  )  ) ,
%	Msgs 
%.

mergePipe (NW1, NW2, X) ->
	% erlang_system_flag(schedulers_online, 56),
	Images = list_merge:imageList(X),
	play2:nest(fun(I) -> list_merge:readImage(I) end, NW1, fun(I) -> list_merge:convertMerge(I) end, NW2, Images).

runPipe(Nw1, Nw2, X) ->
   	io:format("Image Merge Pipe on ~p ~p ~p ~n", [Nw1, Nw2, sk_profile:benchmark(fun ?MODULE:mergePipeFarm/3, [Nw1, Nw2, X], 1)]),
	io:format("Done on ~p and ~p cores ~n." , [Nw1, Nw2]).


