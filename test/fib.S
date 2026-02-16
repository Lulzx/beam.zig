{module, fib}.  %% version = 0

{exports, [{main,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 11}.


{function, main, 0, 2}.
  {label,1}.
    {line,[{location,"fib.erl",4}]}.
    {func_info,{atom,fib},{atom,main},0}.
  {label,2}.
    {allocate,0,0}.
    {move,{integer,20},{x,0}}.
    {line,[{location,"fib.erl",5}]}.
    {call,1,{f,4}}. % fib/1
    {'%',{var_info,{x,0},[{type,{t_integer,{0,'+inf'}}}]}}.
    {call_ext_last,1,{extfunc,erlang,display,1},0}.


{function, fib, 1, 4}.
  {label,3}.
    {line,[{location,"fib.erl",7}]}.
    {func_info,{atom,fib},{atom,fib},1}.
  {label,4}.
    {'%',{var_info,{x,0},[{type,{t_integer,{'-inf',20}}}]}}.
    {select_val,{tr,{x,0},{t_integer,{'-inf',20}}},
                {f,6},
                {list,[{integer,0},{f,5},{integer,1},{f,5}]}}.
  {label,5}.
    return.
  {label,6}.
    {line,[{location,"fib.erl",9}]}.
    {gc_bif,'-',
            {f,0},
            1,
            [{tr,{x,0},{t_integer,{'-inf',20}}},{integer,1}],
            {x,1}}.
    {allocate,1,2}.
    {move,{x,0},{y,0}}.
    {move,{x,1},{x,0}}.
    {call,1,{f,4}}. % fib/1
    {'%',{var_info,{x,0},[{type,{t_integer,{0,'+inf'}}}]}}.
    {gc_bif,'-',
            {f,0},
            1,
            [{tr,{y,0},{t_integer,{'-inf',20}}},{integer,2}],
            {x,1}}.
    {move,{x,0},{y,0}}.
    {move,{x,1},{x,0}}.
    {call,1,{f,4}}. % fib/1
    {'%',{var_info,{x,0},[{type,{t_integer,{0,'+inf'}}}]}}.
    {gc_bif,'+',
            {f,0},
            1,
            [{tr,{y,0},{t_integer,{0,'+inf'}}},
             {tr,{x,0},{t_integer,{0,'+inf'}}}],
            {x,0}}.
    {deallocate,1}.
    return.


{function, module_info, 0, 8}.
  {label,7}.
    {line,[]}.
    {func_info,{atom,fib},{atom,module_info},0}.
  {label,8}.
    {move,{atom,fib},{x,0}}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 10}.
  {label,9}.
    {line,[]}.
    {func_info,{atom,fib},{atom,module_info},1}.
  {label,10}.
    {move,{x,0},{x,1}}.
    {move,{atom,fib},{x,0}}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
