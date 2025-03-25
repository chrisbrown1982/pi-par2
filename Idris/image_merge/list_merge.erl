-module(list_merge).

% -include_lib("erl_img.hrl").

-compile([export_all]).

-define(NW, 8).

-define(IMAGE_JPEG,      image_jpeg).
-define(IMAGE_TIFF,      image_tiff).
-define(IMAGE_GIF,       image_gif).
-define(IMAGE_PNG,       image_png).
-define(IMAGE_BMP,       image_bmp).
-define(IMAGE_X_XPIXMAP, image_x_xpixmap).
-define(IMAGE_UNDEF,     image_undef).
-define(IMAGE_TGA,       image_tga).
-define(VIDEO_MPEG,      video_mpeg).

-define(PAD_Len(L,A), (((A)-((L) rem (A))) rem (A))).

-define(PAD_Len8(L), ((8 - ((L) band 7)) band 7)).

-define(PAD(L,A),
        case ?PAD4_Len(L,A) of
            0 -> <<>>;
            1 -> <<0>>;
            2 -> <<0,0>>;
            3 -> <<0,0,0>>;
            4 -> <<0,0,0,0>>;
            5 -> <<0,0,0,0,0>>;
            6 -> <<0,0,0,0,0,0>>;
            7 -> <<0,0,0,0,0,0,0>>;
            N -> list_to_binary(lists:duplicate(N,0))
        end).

-define(IMAGE_TYPES, [?IMAGE_JPEG,
                      ?IMAGE_TIFF,
                      ?IMAGE_GIF,
                      ?IMAGE_PNG,
                      ?IMAGE_BMP,
                      ?IMAGE_X_XPIXMAP,
                      ?IMAGE_TGA,
                      ?VIDEO_MPEG]).

-record(erl_pixmap,
        {
          top      = 0,
          left     = 0,
          width    = 0,
          height   = 0,
          palette,          %% list [{R,G,B}]
          format,           %% pixmap format
          attributes = [],  %% extension codes
          pixels   = []     %% [ {Ri,binary(Row)} ]
         }).


-record(erl_image,
        {
          type,         %% module name of image handler
          name,         %% Image name (no path)
          filename,     %% Full filename
          size,         %% File size
          extension,    %% extension used
          mtime,        %% file creation date {{YYYY,MM,DD},{HH,MM,SS}}
          itime,        %% image creation date {{YYYY,MM,DD},{HH,MM,SS}}
          comment = "", %% image comment (if present)
          format,       %% pixel format:
                        %%  gray4, gray8,
                        %%  palette4, palette8
                        %%  b8g8r8 r8g8b8 r8g8b8a8
          width,        %% Image width
          height,       %% Image height
          depth,        %% Image depth
          bytes_pp = 3, %% bytes per pixel
          alignment = 1,
          attributes = [], %% list of attributes [{atom(Key),term(Value)}]
          order,        %% sample order left_to_right or right_to_left
          palette,      %% list [{R,G,B}]
          pixmaps = []  %% [#erl_pixmap]
         }).

%%------------------------------------------------------------------------------
%% Debugging 

-ifndef(debug).
-define(debug, true).
%% -define(debug, false).
-endif.

-ifndef(print).
-define(print(Var), case ?debug of
			true ->
			    io:format("~p:~p~n  ~p: ~p~n", 
				      [?MODULE, ?LINE, ??Var, Var]);
			false ->
			    ok
		    end).
-endif.


%%------------------------------------------------------------------------------
%% Worker Utility Functions

-spec removeAlpha(list(), atom()) -> list().

removeAlpha([], _) -> 
    [];
removeAlpha([R,G,B,_ | T], r8g8b8a8) ->
    [R, G, B | removeAlpha(T, r8g8b8a8)];
removeAlpha(Xs, _) ->
    Xs.

-spec convertToWhite(list()) -> list().
convertToWhite([]) -> 
    [];
convertToWhite([R,G,B | T]) when R < 20, G < 20, B < 20 ->
    [ 255,255,255 | convertToWhite(T) ];
convertToWhite([R,G,B | T]) -> 
    [R,G,B | convertToWhite(T)].

-spec mergeTwo(list(), list()) -> list().

mergeTwo([], _) -> 
    [];
mergeTwo(_, []) -> 
    [];
mergeTwo([255,255,255 | T], [R2, G2, B2 | T2]) ->
    [R2,G2,B2 | mergeTwo(T, T2) ];
mergeTwo([R,G,B | T], [_, _, _ | T2]) ->
    [R,G,B | mergeTwo(T,T2)].

%%------------------------------------------------------------------------------
%% Worker Interface Functions

-spec imageList(non_neg_integer()) -> [{string(), string(), string()}].

imageList(0) ->
    [];
imageList(N) ->
    [{"./images/helmetScaled.png", 
      "./images/joeScaled.png", 
      "./images/merged" ++ integer_to_list(N) ++ ".png"} | imageList(N-1)].

-spec readImage({string(), string(), string()}) -> {[list()], [list()], 
						    atom(), atom(), string()}.

readImage({FileName, FileName2, Output}) -> 
    %{ok, _Img=#erl_image{format=F1, pixmaps=[PM]}} = erl_img:load(FileName),
    {ok, F} = erl_img:load(FileName),
    %{ok, _Img=#erl_image{format=F1, pixmaps=[PM]}} = erl_img:load(FileName),
    PM = element(20, F),
    F1 = element(10, F), % F#erl_image.format, 
    
    
    % #erl_pixmap{pixels=Rows} = PM,
    
    
    R = lists:map(fun({_A,B}) -> binary_to_list(B) end, element(9, F)), % Rows),

    %{ok, _Img2=#erl_image{format=F2, pixmaps=[PM2]}} = erl_img:load(FileName2),

    {ok, F22} = erl_img:load(FileName2),
    F2 = element(20, F22), % F22#erl_image.format, 
    PM2 = element(10, F22), % F22#erl_image.pixmaps,
    
    %#erl_pixmap{pixels=Rows2} =PM2,
    R2 = lists:map(fun({_A2,B2}) -> binary_to_list(B2) end, element(9, F22)), % Rows2),
      
    {R, R2, F1, F2, Output}.

-spec convertMerge({[list()], [list()], atom(), 
		    atom(), string()}) -> {[list()], integer(), string()}.

convertMerge({R, R2, F1, F2, Name}) ->
    %% ?print(memsup:get_system_memory_data()),
    %% ?print(erlang:i()),
    R1_p = lists:map(fun(L) -> removeAlpha(L, F1) end, R),
    R2_p = lists:map(fun(L2) -> removeAlpha(L2, F2) end, R2),

    WhiteR =  lists:map(fun(Col) -> convertToWhite(Col) end, R1_p),
  
    Result = lists:zipwith(fun(L1,L2) -> mergeTwo(L1, L2) end, WhiteR, R2_p),

    {Result, length(R), Name};
convertMerge(X) -> io:format("~p~n", [X]).

%%------------------------------------------------------------------------------
%% Interface Functions

-spec merge(non_neg_integer()) -> [{[list()], integer(), string()}].

merge(X) ->
    [convertMerge(readImage(Y)) || Y <- imageList(X)].


run(X) ->
	io:format("Image Merge ~p~n", [sk_profile:benchmark(fun ?MODULE:merge/1, [X], 1)]).


runFarm(Nw, X) ->
    erlang:system_flag(schedulers_online, Nw),
    io:format("Image Merge ~p~n", [sk_profile:benchmark(fun ?MODULE:mergeFarm/2, [Nw, X], 1)]),
    io:format("Done on ~p cores ~n.", [Nw]).  
				   
				   

mergeFarm(Nw, X) ->
    skel:do([{farm, [{seq, fun (Y) -> convertMerge(readImage(Y)) end}],Nw}],imageList(X)).

-spec mergeFarmPipe(non_neg_integer()) -> [{[list()], integer(), string()}].

mergeFarmPipe(X) ->
    skel:do([{farm, [{pipe, [{seq, fun ?MODULE:readImage/1}, 
			     {seq, fun ?MODULE:convertMerge/1}]}], ?NW}],
	    imageList(X)).


mergePipeFarm(Nw1, Nw2, X) ->
    skel:do([{pipe, [{farm, [{seq, fun ?MODULE:readImage/1}], Nw1}, 
		     {farm, [{seq, fun ?MODULE:convertMerge/1}], Nw2}]}],
	    imageList(X)).

runPipe(Nw1, Nw2, X) -> 
    erlang:system_flag(schedulers_online, Nw1 + Nw2),
    io:format("Image Merge Pipe on ~p ~p ~p~n", [Nw1, Nw2, sk_profile:benchmark(fun ?MODULE:mergePipeFarm/3, [Nw1, Nw2, X], 1)]),
    io:format("Done on ~p and ~p cores ~n.", [Nw1, Nw2]).

start() ->
    application:load(sasl),
    application:start(sasl),
    application:start(os_mon).

test() ->
 record_info(fields, erl_image).
