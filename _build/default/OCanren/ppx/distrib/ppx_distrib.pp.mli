Caml1999N031����   %      
   	#OCanren/ppx/distrib/ppx_distrib.mli����  
�   �  �  ˠ����1ocaml.ppx.context��&_none_@@ �A����������)tool_name���*ppx_driver@@@����,include_dirs����"[]@@@����)load_path!����
%@%@@����,open_modules*����.@.@@����+for_package3����$None8@8@@����%debug=����%falseB@B@@����+use_threadsG����
K@K@@����-use_vmthreadsP����T@T@@����/recursive_typesY����]@]@@����)principalb����%f@f@@����3transparent_modulesk����.o@o@@����-unboxed_typest����7x@x@@����-unsafe_string}����@�@�@@����'cookies�����"::�����������,inline_tests�@�@@����'enabled��.<command-line>A@A�A@H@@��A@@�A@I@@@@�@@����������������,library-name�@�@@����+ppx_distrib��A@A�A@L@@��A@M@@@@�@@�������@�@@@�@@�@@@�@@�@@@@�@@@�@�������*ocaml.textǐ������	# {1 Generating reifiers via PPX}   ��	#OCanren/ppx/distrib/ppx_distrib.mliA@@�A@h@@@@@@�����ؐ������
  
  This syntax extension allows to generate reifier 'reify' and 'prj_exn' for user data type. The syntax is the following:

  {[
  [%%ocanren
  type ground =
    | Symb of GT.string
    | Seq of ground Std.List.ground
    [@@deriving gt ~options:{ show; gmap }]
  ]
  ]}

  In the case above the rewriter will generate
  - so-called fully abstract type {[ type ('a, 'b) t = Symb of 'a | Seq of 'b  ]}
  - it is ground instantiation {[ type ground = (GT.string, ground Std.List.ground) t ]}
  - a logic type, to represent user values after reification {[ type logic = ... ]}
  - and injected type, which is inner representation of values during relational search {[ type injected = ... ]}
  - two reifiers to project an answer to ground representation and to logic representation
    {[
      let prj_exn : (injected, ground) OCanren.Reifier.t = ...
      let reify : (injected, logic) OCanren.Reifier.t = ...
    ]}

  If you need more control of generated types, you could manually specify instantiation fully abstract type to ground one. For example;
  {[
  [%%ocanren
  type nonrec ('a, 'b) t =
    | Nil
    | Cons of 'a * 'b
    [@@deriving gt ~options:{ show; gmap }]
  type 'a ground = ('a, 'a ground) t
  ]
  ]}

  In the examples on this page a {v [@@deriving ...] v} is not mandatory, this user-defined attribute is thread through generated type definitions. Although, the generation of reifiers requires an `fmap` for our fully abstract type, thaty's why {v [@@deriving gt ~options:{ gmap }] v} is important. At the moment it is not possible to specify 'fmap' via other PPX syntax extension.

  See also: Camlp5 syntax extension {!module-"OCanren.Pa_ocanren"} (currenly, I don't know how to specify a link to another package, it should be avaiable at {{:../../OCanren/Pa_ocanren/index.html}here}.

��Cjj�i>@@@@@@@@