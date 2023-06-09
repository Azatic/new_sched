Caml1999M031����   "      
   	 OCanren/ppx/tester/ppx_tester.ml����  *�  
	  $  #F�����1ocaml.ppx.context��&_none_@@ �A����������)tool_name���*ppx_driver@@@����,include_dirs����"[]@@@����)load_path!����
%@%@@����,open_modules*����.@.@@����+for_package3����$None8@8@@����%debug=����%falseB@B@@����+use_threadsG����
K@K@@����-use_vmthreadsP����T@T@@����/recursive_typesY����]@]@@����)principalb����%f@f@@����3transparent_modulesk����.o@o@@����-unboxed_typest����7x@x@@����-unsafe_string}����@�@�@@����'cookies�����"::�����������,library-name�@�@@����*ppx_tester��.<command-line>A@A�A@K@@��A@@�A@L@@@@�@@�������@�@@@�@@�@@@@�@@@�@�������*ocaml.text��������
  �
  An extension that allows not to write errornous qh, qrh and stuff like that.
  It looks at number of lambdas in the last argument, and insert numberals as penultimate argument.

  Expands

    {[ let __ _ = [%tester runR OCanren.reify show_int show_intl (fun q -> q === !!1)] ]}

  to

  {[
    let __ _ =
      runR OCanren.reify show_int show_intl q qh
        ("<string repr of goal>", (fun q -> q === (!! 1)))
  ]}

��	 OCanren/ppx/tester/ppx_tester.mlH � ��XFH@@@@@@��������&Ppxlib��ZJO�ZJU@�@@A��ZJJ@@�@���@�����4string_of_expression��\W[�\Wo@�@@@��@@���!e��'\Wp�(\Wq@�@@@�  �������&Format*set_margin��6]tv�7]t�@�@@@��@���$1000@��@]t��A]t�@@@@�@@@�  �������&Format.set_max_indent��O^���P^��@�@@@��@���!0@��Y^���Z^��@@@@�@@@��@�����#ans��e_���f_��@�@@@�������&Format(asprintf��r_���s_��@�@@@��@���"%a��|_���}_��@@��_����_��@@@��@�����)Pprintast*expression���_����_��@�@@@��@����!e���_����_��@�@@@@�(@@@@���_��@@����#ans���`����`��@�@@@�@@@�X@@@�r@@@��A@@@���\WW@@�	@���@�����$name���c����c��@�@@@���&tester���c����c� @@���c����c�@@@@���c��@@�@���@������"()���e��e	@@�@@@��@�����*extensions���f��f@�@@@��@�����'pattern���g'��g.@�@@@�  !�����+Ast_pattern���h1@��h1K@�@@A���h1;@@������$pstr��iOU�iOY@�@@@��@������#^::��iO|�iO@�@@@��@������)pstr_eval��iO[�iOd@�@@@��@������*pexp_apply��)iOf�*iOp@�@@@��@����"__��4iOq�5iOs@�@@@��@����"__��?iOt�@iOv@�@@@@��CiOe�DiOw@��@@@��@����#nil��OiOx�PiO{@�@@@@�7@@@��@����#nil��[iO��\iO�@�@@@@��_iOZ�`iO�@��G@@@@�b@@@��eh17@@@@��gg#@@����"::��nk���o U	>	CA�����������)Extension'declare��~k��@�@@@��@����$name���l����l��@�@@@��@������)Extension'Context*Expression���m����m��@@�@@@��@����'pattern���n����n��@�@@@��@�Đ#loc@������o����o��@�@@@�Đ$path@�@���o����o��@@@��@@���!f���o� ��o�@�@@@��@@���$args���o���o�@�@@@�  !�������&Ppxlib+Ast_builder'Default���p
��p
5@�@@A���p
@@��@��������*rev_prefix���q9E��q9O@�@@@����$last���q9Q��q9U@�@@@@�@@@������$args��rXh�rXl@�@@@������"[]��sr~�sr�@@�@@@@������(failwith��sr��sr�@�@@@��@���1should not happen��!sr��"sr�@@��$sr��%sr�@@@@�@@@�����"xs��.t���/t��@�@@@@���������$List#rev��=u���>u��@�@@@��@����"xs��Hu���Iu��@�@@@@�@@@��������Sv���Tv��@��@������!h��_v���`v��@�@@@����"tl��hv���iv��@�@@@@�A@@�@@@@�������"tl��vv���wv��@�@@@�����!h���v����v��@�@@@@�@@@����������w���w�@@�@@@@������(failwith���w���w�@�@@@��@���1should not happen���w���w�'@@���w���w�(@@@@�@@@@���u����w�)@����u��@@@@���rXb@@@@���q9A@@��@�����%count���y5A��y5F@�@@@��A�����&helper���zI[��zIa@�@@@��@@���#acc���zIb��zIe@�@@@��@@���!e���zIf��zIg@�@@@��������!e���{j|��{j}@�@@@��)pexp_desc���{j~��{j�@�
@@@������(Pexp_fun���|����|��@��@����@��|���|��@@@��@��|���|��@@@��@��|���|��@@@����$body��|���|��@�@@@@��|���|��@��@@@�$@@@@������&helper��$|���%|��@�@@@��@������!+��1|���2|��@�@@@��@���!1@��;|���<|��@@@��@����#acc��E|���F|��@�@@@@��I|���J|��@��@@@��@����$body��U|���V|��@�@@@@�5@@@���@��]}���^}��@@@@����#acc��e}���f}��@�@@@@��i{jv@@@��A@@��A@@@��mzIS@@������&helper��v���w�@�@@@��@���!0@�������@@@��@������#snd�������@�@@@��@����$last����	���@�@@@@�������@��@@@@�*@@@�4@@@@���y5=@@��@�����&middle��� A&�� A,@�@@@������"@@��� CXb�� CXd@�@@@��@�������$List#map��� B/9�� B/A@�@@@��@��@@���!e��� B/G�� B/H@�@@@�������'Nolabel��� B/L�� B/S@@�@@@�����!e��� B/U�� B/V@�@@@@�@@@��� B/B�� B/W@���� B/C	@@@@�-@@@��@������%count��� Deu�� Dez@�@@@�����!0@�� E��� E��@@@@������(failwith�� E��� E��@�@@@��@���*Bad syntax�� E��� E��@@�� E��� E��@@@@�@@@�����!1@��( F���) F��@@@@����°�/ F���0 F��A����������)pexp_desc��= F��A����*Pexp_ident�������#txt����$Ldot��������&Lident����'OCanren"@"@@"@@����!q'@'@@@'@@'@@����#loc,����#loc�?1A@@@@2@@2@@����(pexp_loc7����#loc�J<A@@����.pexp_loc_stackB����"[]G@G@@����/pexp_attributesL����
P@P@@@@P@@�����%��� F��cA����������b��� F��A����a�������`����V����"qh@@@@@����P����#loc�+A@@@@ @@ @@����O$����#loc�5)A@@����N.����M2@2@@����L6����U:@:@@@@:@@�����Ұ�� F���A@��A@@@�N�A@@�O�A@@@���A@@��� F���@@@�����!2@��� G���� G��@@@@�������� G���� G�A����������ð�� G��A�������������������������������'OCanren@@@@@����"qr#@#@@@#@@#@@�����'����#loc�9,A@@@@-@@-@@�����1����#loc�C6A@@�����;�����?@?@@�����C�����G@G@@@@G@@�����ް�K G�YA������������W G�A�������������������#qrh@@@@@����	����#loc�+A@@@@ @@ @@����$����#loc�5)A@@����.����2@2@@����6����:@:@@@@:@@��������� G��A@��A@@@�N�A@@�O�A@@@���A@@��� G���@@@�����!3@��� H�� H@@@@����>��� H"�� HEA����������|��� H5A����{�������z����y��������x����'OCanren@@@@@����#qrs#@#@@@#@@#@@����w'����#loc�9,A@@@@-@@-@@����v1����#loc�C6A@@����u;����t?@?@@����sC����|G@G@@@@G@@�������� H7YA����������԰� HCA����������������������$qrsh@@@@@���������#loc�+A@@@@ @@ @@�����$����#loc�5)A@@�����.�����2@2@@�����6�����:@:@@@@:@@�����D��O HD�A@��A@@@�N�A@@�O�A@@@���A@@��U H �@@@�����!4@��] IFR�^ IFS@@@@�������d IFY�e IF~A����������5��q IFmA����4�������3����2��������1����'OCanren@@@@@����$qrst#@#@@@#@@#@@����0'����#loc�9,A@@@@-@@-@@����/1����#loc�C6A@@����.;����-?@?@@����,C����5G@G@@@@G@@�����P��� IFoYA�������������� IF|A����������������������%qrsth@@@@@����{����#loc�+A@@@@ @@ @@����z$����#loc�5)A@@����y.����x2@2@@����w6�����:@:@@@@:@@�������� IF}�A@��A@@@�N�A@@�O�A@@@���A@@�� IFW�@@@���@�� J�� J�@@@@������(failwith�� J�� J�@�@@@��@�������&Printf'sprintf��, J��- J�@�@@@��@���	&5 and more arguments are not supported��6 J��7 J�@@��9 J��: J�@@@@��< J��= J�@��@@@@�$@@@@��B Deo@@@@�~@@@@��E A"	@@��@�����$last��O L���P L��@�@@@��@�����!s��[ M���\ M� @�@@@������"@@��f M��g M�@�@@@��@����4string_of_expression��q M��r M�@�@@@��@������#snd��~ M�� M�@�@@@��@����$last��� M��� M�#@�@@@@�@@@@�@@@@��� M��@@�  !�������&Ppxlib+Ast_builder'Default��� N':�� N'T@�@@A��� N'5@@������m��� OXb�� OX�A����*Pexp_tuple�����"::����������-pexp_constant��� OXm�� OXz@�@@@���#loc������� OX|�� OX@�@@@��@����-Pconst_string��� OX��� OX�@��������!s��� OX��� OX�@�@@@�����#loc��� OX��� OX�@�@@@�����$None��� OX��� OX�@@�@@@@��� OX��� OX�@��@@@�� OX�� OX�@��-@@@@�E@@@�����Wd����������#snd�� OX�� OX�@�@@@��@����$last��# OX��$ OX�@�@@@@�@@@�������@�@@@�@@�@@@�@@�@@�@@����������#loc���A@@������������@�@@������������@�@@@@�@@��G N'1�@@@���@@@@��J L���@@������*pexp_apply��S Q���T Q��@�@@@���#loc������_ R���` R��@�@@@��@����!f��j S���k S��@�@@@��@������"@@��w T�	�x T�	@�@@@��@�������$List*rev_append��� T���� T�	@�@@@��@����*rev_prefix��� T�	�� T�	@�@@@@�@@@��@�������$List&concat��� T�	�� T�	@�@@@��@����>��� T�	 �� T�	;A��������&middle��� T�	&@�@@@�����R��� T�	(A��������\��� T�	*�� T�	9A�����������'Nolabel��� T�	1@@�@@@�����$last��� T�	3�� T�	7@�@@@@�@@@�������� T�	8"A@�#A@@@�%$A@@�0%@@@�������� T�	:JA@�KA@@@�9LA@@�:MA@@@�ONA@@��� T�	P@@@@�\Q@@@@��� T���� T�	<@��|V@@@@��@@@��@@@��@@@�d@@@�X@@@��	p

@@@�?A@@�JA@@��	o��A@@��	o���	 T�	=@���	o��@@@@��@@@�������	 U	>	B�A@��A@@@���A@@��	k���@@@���@@@@��	!f�@@��������&Ppxlib&Driver7register_transformation��	. W	I	K�	/ W	I	p@�@@@���*extensions������	: W	I	r�	; W	I	|@�@@@��@����$name��	E W	I	}�	F W	I	�@�@@@@�@@@�)@@@@��	Ke@@�@@