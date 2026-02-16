{module, spawn_test}.  %% version = 0

{exports, [{main,0},{module_info,0},{module_info,1},{worker,1}]}.

{attributes, []}.

{labels, 12}.


{function, main, 0, 2}.
  {label,1}.
    {line,[{location,"spawn_test.erl",4}]}.
    {func_info,{atom,spawn_test},{atom,main},0}.
  {label,2}.
    {allocate,0,0}.
    {move,{atom,worker},{x,1}}.
    {move,{literal,[hello]},{x,2}}.
    {move,{atom,spawn_test},{x,0}}.
    {line,[{location,"spawn_test.erl",5}]}.
    {call_ext,3,{extfunc,erlang,spawn,3}}.
    {move,{literal,{greeting,world}},{x,1}}.
    {line,[{location,"spawn_test.erl",6}]}.
    send.
    {move,{atom,done},{x,0}}.
    {line,[{location,"spawn_test.erl",7}]}.
    {call_ext_last,1,{extfunc,erlang,display,1},0}.


{function, worker, 1, 4}.
  {label,3}.
    {line,[{location,"spawn_test.erl",9}]}.
    {func_info,{atom,spawn_test},{atom,worker},1}.
  {label,4}.
    {allocate,1,1}.
    {move,{x,0},{y,0}}.
  {label,5}.
    {loop_rec,{f,7},{x,0}}.
    {test,is_tagged_tuple,{f,6},[{x,0},2,{atom,greeting}]}.
    {test_heap,3,1}.
    {get_tuple_element,{x,0},1,{x,0}}.
    remove_message.
    {put_tuple2,{x,0},{list,[{y,0},{x,0}]}}.
    {line,[{location,"spawn_test.erl",12}]}.
    {call_ext_last,1,{extfunc,erlang,display,1},1}.
  {label,6}.
    {loop_rec_end,{f,5}}.
  {label,7}.
    {wait,{f,5}}.


{function, module_info, 0, 9}.
  {label,8}.
    {line,[]}.
    {func_info,{atom,spawn_test},{atom,module_info},0}.
  {label,9}.
    {move,{atom,spawn_test},{x,0}}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 11}.
  {label,10}.
    {line,[]}.
    {func_info,{atom,spawn_test},{atom,module_info},1}.
  {label,11}.
    {move,{x,0},{x,1}}.
    {move,{atom,spawn_test},{x,0}}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
