Module:    dylan-user
Copyright:    Original Code is Copyright (c) 1995-2004 Functional Objects, Inc.
              All rights reserved.
License:      See License.txt in this distribution for details.
Warranty:     Distributed WITHOUT WARRANTY OF ANY KIND

/// See the Integers proposal in Dylan Notebook\DylanWorks\Runtime\Integers\Integers ...

define library big-integers
  use dylan;
  use common-dylan, import: { common-extensions };

  export big-integers;
end library big-integers;

define module big-integers
  use dylan-arithmetic, export: all;
  use dylan-extensions,
    import: {<double-integer>, <machine-word>},
    export: all;
end module big-integers;

define module big-integers-internal
  use dylan-excluding-arithmetic;
  use dylan-arithmetic;
  use machine-word-lowlevel;
  use big-integers;
  use dylan-primitives;
  use dylan-extensions;
  use common-extensions,
    import: {number-to-string, machine-word-to-string};
end module big-integers-internal;
