{module, list_ops}.  %% version = 0

{exports, [{main,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 15}.


{function, main, 0, 2}.
  {label,1}.
    {line,[{location,"list_ops.erl",4}]}.
    {func_info,{atom,list_ops},{atom,main},0}.
  {label,2}.
    {allocate,0,0}.
    {move,{literal,[1,2,3,4,5]},{x,0}}.
    {line,[{location,"list_ops.erl",5}]}.
    {call,1,{f,4}}. % sum/1
    {'%',{var_info,{x,0},[{type,{t_integer,{1,'+inf'}}}]}}.
    {call_ext,1,{extfunc,erlang,display,1}}.
    {move,{literal,[1,2,3,4,5]},{x,0}}.
    {line,[{location,"list_ops.erl",6}]}.
    {call,1,{f,7}}. % reverse/1
    {'%',{var_info,{x,0},[{type,{t_list,{t_integer,{1,5}},nil}}]}}.
    {call_ext_last,1,{extfunc,erlang,display,1},0}.


{function, sum, 1, 4}.
  {label,3}.
    {line,[{location,"list_ops.erl",8}]}.
    {func_info,{atom,list_ops},{atom,sum},1}.
  {label,4}.
    {'%',{var_info,{x,0},[{type,{t_list,{t_integer,{1,5}},nil}}]}}.
    {test,is_nonempty_list,{f,5},[{x,0}]}.
    {allocate,1,1}.
    {get_list,{x,0},{y,0},{x,0}}.
    {line,[{location,"list_ops.erl",9}]}.
    {call,1,{f,4}}. % sum/1
    {'%',{var_info,{x,0},[{type,{t_integer,{0,'+inf'}}}]}}.
    {gc_bif,'+',
            {f,0},
            1,
            [{tr,{y,0},{t_integer,{1,5}}},{tr,{x,0},{t_integer,{0,'+inf'}}}],
            {x,0}}.
    {deallocate,1}.
    return.
  {label,5}.
    {move,{integer,0},{x,0}}.
    return.


{function, reverse, 1, 7}.
  {label,6}.
    {line,[{location,"list_ops.erl",11}]}.
    {func_info,{atom,list_ops},{atom,reverse},1}.
  {label,7}.
    {'%',{var_info,{x,0},[{type,{t_cons,{t_integer,{1,5}},nil}}]}}.
    {move,nil,{x,1}}.
    {call_only,2,{f,9}}. % reverse/2


{function, reverse, 2, 9}.
  {label,8}.
    {line,[{location,"list_ops.erl",12}]}.
    {func_info,{atom,list_ops},{atom,reverse},2}.
  {label,9}.
    {'%',{var_info,{x,0},[{type,{t_list,{t_integer,{1,5}},nil}}]}}.
    {'%',{var_info,{x,1},[{type,{t_list,{t_integer,{1,5}},nil}}]}}.
    {test,is_nonempty_list,{f,10},[{x,0}]}.
    {test_heap,2,2}.
    {get_list,{x,0},{x,2},{x,0}}.
    {put_list,{x,2},{x,1},{x,1}}.
    {call_only,2,{f,9}}. % reverse/2
  {label,10}.
    {move,{x,1},{x,0}}.
    return.


{function, module_info, 0, 12}.
  {label,11}.
    {line,[]}.
    {func_info,{atom,list_ops},{atom,module_info},0}.
  {label,12}.
    {move,{atom,list_ops},{x,0}}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 14}.
  {label,13}.
    {line,[]}.
    {func_info,{atom,list_ops},{atom,module_info},1}.
  {label,14}.
    {move,{x,0},{x,1}}.
    {move,{atom,list_ops},{x,0}}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
