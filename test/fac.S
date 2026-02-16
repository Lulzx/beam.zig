{module, fac}.  %% version = 0

{exports, [{main,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 10}.


{function, main, 0, 2}.
  {label,1}.
    {line,[{location,"fac.erl",4}]}.
    {func_info,{atom,fac},{atom,main},0}.
  {label,2}.
    {allocate,0,0}.
    {move,{integer,10},{x,0}}.
    {line,[{location,"fac.erl",5}]}.
    {call,1,{f,4}}. % fac/1
    {'%',{var_info,{x,0},[{type,{t_integer,any}}]}}.
    {call_ext_last,1,{extfunc,erlang,display,1},0}.


{function, fac, 1, 4}.
  {label,3}.
    {line,[{location,"fac.erl",7}]}.
    {func_info,{atom,fac},{atom,fac},1}.
  {label,4}.
    {'%',{var_info,{x,0},[{type,{t_integer,{'-inf',10}}}]}}.
    {test,is_eq_exact,{f,5},[{tr,{x,0},{t_integer,{'-inf',10}}},{integer,0}]}.
    {move,{integer,1},{x,0}}.
    return.
  {label,5}.
    {line,[{location,"fac.erl",8}]}.
    {gc_bif,'-',
            {f,0},
            1,
            [{tr,{x,0},{t_integer,{'-inf',10}}},{integer,1}],
            {x,1}}.
    {allocate,1,2}.
    {move,{x,0},{y,0}}.
    {move,{x,1},{x,0}}.
    {call,1,{f,4}}. % fac/1
    {'%',{var_info,{x,0},[{type,{t_integer,any}}]}}.
    {gc_bif,'*',
            {f,0},
            1,
            [{tr,{y,0},{t_integer,{'-inf',10}}},{tr,{x,0},{t_integer,any}}],
            {x,0}}.
    {deallocate,1}.
    return.


{function, module_info, 0, 7}.
  {label,6}.
    {line,[]}.
    {func_info,{atom,fac},{atom,module_info},0}.
  {label,7}.
    {move,{atom,fac},{x,0}}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 9}.
  {label,8}.
    {line,[]}.
    {func_info,{atom,fac},{atom,module_info},1}.
  {label,9}.
    {move,{x,0},{x,1}}.
    {move,{atom,fac},{x,0}}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
