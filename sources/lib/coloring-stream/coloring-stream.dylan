Module:    coloring-stream-internals
Author:    Bruce Mitchener, Jr.
Copyright: Original Code is Copyright 2015 Dylan Hackers.
           All rights reserved.
License:   See License.txt in this distribution for details.
Warranty:  Distributed WITHOUT WARRANTY OF ANY KIND

define sealed abstract class <coloring-stream> (<wrapper-stream>)
end class <coloring-stream>;

define sealed domain make(singleton(<coloring-stream>));
define sealed domain initialize(<coloring-stream>);

define sealed method make
    (class == <coloring-stream>, #rest initargs,
     #key inner-stream :: <stream>)
 => (coloring-stream :: <coloring-stream>)
  let stream-class = coloring-stream-class-for-stream(inner-stream);
  apply(make, stream-class, initargs)
end method make;

define generic coloring-stream-class-for-stream
    (stream :: <stream>)
 => (coloring-stream-class :: <class>);

define method coloring-stream-class-for-stream
    (stream :: <stream>)
 => (coloring-stream-class :: <class>)
  <null-coloring-stream>
end method coloring-stream-class-for-stream;

define method coloring-stream-class-for-stream
    (stream :: <file-stream>)
 => (coloring-stream-class :: <class>)
  if (stream-supports-color?(stream))
    <ansi-coloring-stream>
  else
    <null-coloring-stream>
  end if
end method coloring-stream-class-for-stream;

define method colorize-stream
    (stream :: <stream>,
     #key force-ansi? = #f)
 => (coloring-stream :: <coloring-stream>)
  if (force-ansi?)
    make(<ansi-coloring-stream>, inner-stream: stream)
  else
    make(<coloring-stream>, inner-stream: stream)
  end if
end;

define method stream-supports-color?
    (stream :: <stream>)
 => (well? :: <boolean>)
  #f
end method stream-supports-color?;

define method stream-supports-color?
    (stream :: <file-stream>)
 => (well? :: <boolean>)
  stream-console?(stream) &
    (environment-variable("TERM") ~== "dumb") &
    (environment-variable("EMACS") ~== "t")
end method stream-supports-color?;

define class <null-coloring-stream> (<coloring-stream>)
end class <null-coloring-stream>;

define method print-object
    (attributes :: <text-attributes>,
     stream :: <coloring-stream>)
 => ()
  ignore(attributes, stream);
end method print-object;