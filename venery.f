( --- Collections. --- )
\ TODO:  
\ COPY
\ JOIN

vocabulary venery
: venery-internal  only forth also venery definitions ;
: venery-public  only forth definitions also venery ;

venery-internal
    0 value xt
    : /allot  here over allot swap erase ;
    : ?execute  ?dup if execute then ;
    : bounds  over + swap ;
    : ?move  dup if move else drop drop drop then ;
    : sfield  ( struct bytes - <name> )  ( adr - adr+n )
    create over @ ,  swap +!  does> @ + ;
    : svar  cell sfield ;
    : struct  variable ;
    : sembed  @ sfield ;
    : *struct  here swap @ /allot ;
    [undefined] bytes [if] : bytes ; [then]

    struct %collection
        %collection svar collection.vtable
        %collection svar collection.length
        %collection svar collection.capacity

    : vector  ( n - <name> n+cell )  ( ??? collection - ??? )
        create dup , cell+  does> @ over collection.vtable @ + @ ?execute ;

    : vtable  ( n - <name> collection 0 )  
        create here swap cells /allot 0 ;
        
    : :vector  ( collection n - <code> ; collection n+1 )
        2dup :noname -rot cells + ! 1 + ;


venery-public

0
vector []  ( n collection -- adr )
vector truncate  ( n collection -- )
vector push  ( item collection -- )
vector pop  ( collection -- item )
vector each  ( xt collection -- )  ( adr -- )
vector delete  ( index count collection -- )
vector .each  ( collection -- )
vector indexof  ( index item collection -- index )  
constant collection-vtable-size

: length  ( collection -- n )
    collection.length @ ;

: inbounds?  ( n collection -- flag )
    length < ;
    
: capacity  ( collection -- n )
    collection.capacity @ ;

: vacate  ( collection -- )
    0 swap truncate ;

: >top  ( collection -- adr )
    dup length 1 - swap [] ;

: pushes  ( ... n collection - )
    locals| s |  0 ?do  s push  loop ;

: pops  ( n collection - ... ) 
    locals| s |  0 ?do  s pop  loop ;

: each>  r> code> swap each ;


: some  ( xt filter-xt collection -- )  ( adr -- )  ( adr -- flag )
;
: diff  ( xt filter-xt collection -- )  ( adr -- )  ( adr -- flag )
;


( Array )
struct %array
    %array %collection sembed array.collection
    %array svar array.data

collection-vtable-size vtable array-vtable  ( collection 0 )
    \ vector []  ( index collection -- adr )
    :vector  array.data @ swap cells + ; 
    \ vector truncate  ( n collection -- )
    :vector  collection.length dup @ rot min swap ! ;
    \ vector push  ( item collection -- )
    :vector  >r  r@ length  r@ [] !  1 r> collection.length +! ;
    \ vector pop  ( collection -- item )
    :vector  >r  r@ length 1 -  r@ [] @   -1 r> collection.length +! ;
    \ vector each  ( xt collection -- )  ( adr -- )
    :vector  xt >r swap to xt dup array.data @ swap length cells bounds ?do
        i xt execute cell +loop r> to xt ; 
    \ vector delete  ( index count collection -- )
    :vector  3dup nip length >= if 3drop exit then
        locals| c n i |
        i n + c length min i - to n  \ adjust count if needed
        i cells c array.data @ +  \ dest
        dup n cells +  \ src
        swap  \ src dest
        c array.data @ c length cells + \ end
        over - ?move
        n negate c collection.length +! ;
    \ vector .each  ( collection -- )
    :vector  dup length . ." items: " each> ? ;
    \ vector indexof  ( index item collection -- index | -1 )  
    :vector  locals| c itm |
        begin  dup c inbounds? while
            dup c [] @ itm = ?exit
            1 +
        repeat
        drop -1 ; 
2drop

: *array  ( n -- array )  %array *struct >r array-vtable r@ collection.vtable !
    here r@ array.data !  dup r@ collection.length !  dup r@
    collection.capacity !  cells /allot  r> ;
: *stack  ( n -- array )  %array *struct >r array-vtable r@ collection.vtable !
    here r@ array.data !  0 r@ collection.length !  dup r@
    collection.capacity !  cells /allot  r> ;

( String )
struct %string
    %string %collection sembed string.collection
    %string svar string.data

collection-vtable-size vtable string-vtable  ( collection 0 )
    \ vector []  ( index collection -- adr )
    :vector  array.data @ swap bytes + ; 
    \ vector truncate  ( n collection -- )
    :vector  collection.length dup @ rot min swap ! ;
    \ vector push  ( item collection -- )
    :vector  >r  r@ length  r@ [] c!  1 r> collection.length +! ;
    \ vector pop  ( collection -- item )
    :vector  >r  r@ length 1 -  r@ [] c@   -1 r> collection.length +! ;
    \ vector each  ( xt collection -- )  ( adr -- )
    :vector  xt >r swap to xt dup string.data @ swap length bounds ?do
        i xt execute 1 bytes +loop r> to xt ; 
    \ vector delete  ( index count collection -- )
    :vector  3dup nip length >= if 3drop exit then
        locals| c n i |
        i n + c length min i - to n  \ adjust count if needed
        i bytes c string.data @ +  \ dest
        dup n bytes +  \ src
        swap  \ src dest
        c string.data @ c length bytes + \ end
        over - ?move
        n negate c collection.length +! ;
    \ vector .each  ( collection -- )
    :vector  dup string.data @ swap length dup . ." : "  type ;
    \ vector indexof  ( index item collection -- index | -1 )  
    :vector  locals| c itm |
        begin  dup c inbounds? while
            dup c [] c@ itm = ?exit
            1 +
        repeat
        drop -1 ;
2drop

: *empty-string  ( n -- string )
    %string *struct >r
    string-vtable r@ collection.vtable !
    here dup r@ string.data !  over /allot
    r@ collection.capacity ! 
    r> ;

: set-string  ( adr n string - )
    >r
    2dup r@ string.data @ swap move
    nip
    r> collection.length !
;

: *string  ( adr n -- string )  \ data will be copied
    *empty-string >r
    r@ set-string
    r> ;


( Node tree )
struct %node
    %node %collection sembed node.collection
    %node svar node.parent
    %node svar node.first
    %node svar node.last
    %node svar node.previous
    %node svar node.next



collection-vtable-size vtable node-vtable  ( collection 0 )
    \ vector []  ( index node -- node|0 )
    :vector
        dup length 0 = if 2drop 0 exit then 
        node.first @ swap 0 ?do node.next @ loop ; 
    \ vector truncate  ( n collection -- )
    :vector
        locals| c n |
        c length n do i c delete loop 
        n c collection.length dup @ rot min swap ! ;
    \ vector push  ( item collection -- )
    :vector  >r  r@ length  r@ [] c!  1 r> collection.length +! ;
    \ vector pop  ( collection -- item )
    :vector  >r  r@ length 1 -  r@ [] c@   -1 r> collection.length +! ;
    \ vector each  ( xt collection -- )  ( adr -- )
    :vector  xt >r swap to xt dup string.data @ swap length bounds ?do
        i xt execute 1 bytes +loop r> to xt ; 
    \ vector delete  ( index count collection -- )
    :vector  3dup nip length >= if 3drop exit then
        locals| c n i |
        i n + c length min i - to n  \ adjust count if needed
        i bytes c string.data @ +  \ dest
        dup n bytes +  \ src
        swap  \ src dest
        c string.data @ c length bytes + \ end
        over - ?move
        n negate c collection.length +! ;
    \ vector .each  ( collection -- )
    :vector  dup string.data @ swap length dup . ." : "  type ;
    \ vector indexof  ( index item collection -- index | -1 )  
    :vector  locals| c itm |
        begin  dup c inbounds? while
            dup c [] c@ itm = ?exit
            1 +
        repeat
        drop -1 ;
2drop

only forth definitions

\ test
create s 100 *stack drop
: numbers  locals| c |  c vacate  c capacity 0 do  i c push  loop ;
s numbers