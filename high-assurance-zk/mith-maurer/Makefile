.PHONY: check build extract

MAURER_IMPL := ../implementation-maurer/src/MPC/Maurer

extract: 
	ecml -i AllCore -O NextMsgECPervasive -q Logic -t option -t odflt -t oget -t is_none -t omap -t oapp -t transpose -t idfun -o $(MAURER_IMPL)/NextMsgECLogic.ml	
	ecml -I proof/EC -i AllCore -i Aux -t Aux -r sample -O NextMsgECInt -O NextMsgECPervasive -O NextMsgECList -O NextMsgECLogic -o $(MAURER_IMPL)/NextMsgECCore.ml
	ecml -I Jasmin:jasmin/eclib -I proof/Maurer -I proof/NextMsg -I proof/EC -I proof/abstract -i NextMsgMaurerP -t MaurerP -O NextMsgECCore -O NextMsgECPervasive -O NextMsgECList -o $(MAURER_IMPL)/NextMsgMaurerP.ml
	ecml -I Jasmin:jasmin/eclib -I proof/Maurer -I proof/Maurer/lib -I proof/MitH -I proof/NextMsg -I proof/NextMsgMaurer -I proof/EC -I proof/abstract -i NextMsgMaurer -t MaurerAdd -t MaurerSMul -t MaurerConst -t MaurerMul -t MaurerGate -t MaurerCircuit -t MaurerReveal -O NextMsgECList -O NextMsgECPervasive -O NextMsgECCore -O NextMsgECInt -O NextMsgECLogic -O NextMsgMaurerP -O NextMsgArray -O NextMsgMaurerAPI -o $(MAURER_IMPL)/NextMsgMaurerProtocol.ml
	ecml -I Jasmin:jasmin/eclib -I proof/Maurer -I proof/Maurer/lib -I proof/MitH -I proof/NextMsg -I proof/NextMsgMaurer -I proof/EC -I proof/abstract -i NextMsgMaurerCompat -i NextMsgMaurer -t MaurerDomain -t MaurerProtocolFunctionality -t MaurerProtocol -t MaurerBoolProtocol -r f -r simulator -r gen_rand -r from_corrupted_parties_t -r from_corrupted_inputs_t -r to_corrupted_views_t -O NextMsgECPervasive -O NextMsgECLogic -O NextMsgECList -O NextMsgECInt -O NextMsgECCore -O NextMsgMaurerP -O NextMsgMaurerAPI -O NextMsgMaurerProtocol -o $(MAURER_IMPL)/NextMsgMaurerCompat.ml

clean:
	rm -rf Print.ec Print.eco Temp.ec
	find . -name "*.eco" -type f -delete
ECFILES := $(shell find proof -type f -name "*.ec")

check: 
	for file in $(ECFILES) ; do \
		echo $$file;  \
		easycrypt compile -I jasmin/src -I Jasmin:jasmin/eclib -I JasminExtra:jasmin/eclib_extra -I proof/concrete -I proof/EC -I proof/Maurer/FieldOps -I proof/Maurer/lib -I proof/Maurer -I proof/MitH -I proof/NextMsg -I proof/NextMsgMaurer $$file -timeout 10 > /dev/null ; \
		if [ $$? -ne 0 ]; then \
			exit 1; \
		fi \
	done; \
