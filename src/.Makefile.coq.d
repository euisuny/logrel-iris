axioms.vo axioms.glob axioms.v.beautified axioms.required_vo: axioms.v 
axioms.vio: axioms.v 
axioms.vos axioms.vok axioms.required_vos: axioms.v 
header_extensible.vo header_extensible.glob header_extensible.v.beautified header_extensible.required_vo: header_extensible.v 
header_extensible.vio: header_extensible.v 
header_extensible.vos header_extensible.vok header_extensible.required_vos: header_extensible.v 
fintype.vo fintype.glob fintype.v.beautified fintype.required_vo: fintype.v axioms.vo
fintype.vio: fintype.v axioms.vio
fintype.vos fintype.vok fintype.required_vos: fintype.v axioms.vos
syntax.vo syntax.glob syntax.v.beautified syntax.required_vo: syntax.v fintype.vo header_extensible.vo
syntax.vio: syntax.v fintype.vio header_extensible.vio
syntax.vos syntax.vok syntax.required_vos: syntax.v fintype.vos header_extensible.vos
lang.vo lang.glob lang.v.beautified lang.required_vo: lang.v 
lang.vio: lang.v 
lang.vos lang.vok lang.required_vos: lang.v 
rules.vo rules.glob rules.v.beautified rules.required_vo: rules.v lang.vo
rules.vio: rules.v lang.vio
rules.vos rules.vok rules.required_vos: rules.v lang.vos
typing.vo typing.glob typing.v.beautified typing.required_vo: typing.v lang.vo
typing.vio: typing.v lang.vio
typing.vos typing.vok typing.required_vos: typing.v lang.vos
logrel.vo logrel.glob logrel.v.beautified logrel.required_vo: logrel.v lang.vo typing.vo
logrel.vio: logrel.v lang.vio typing.vio
logrel.vos logrel.vok logrel.required_vos: logrel.v lang.vos typing.vos
soundness.vo soundness.glob soundness.v.beautified soundness.required_vo: soundness.v fundamental.vo
soundness.vio: soundness.v fundamental.vio
soundness.vos soundness.vok soundness.required_vos: soundness.v fundamental.vos
fundamental.vo fundamental.glob fundamental.v.beautified fundamental.required_vo: fundamental.v logrel.vo rules.vo
fundamental.vio: fundamental.v logrel.vio rules.vio
fundamental.vos fundamental.vok fundamental.required_vos: fundamental.v logrel.vos rules.vos
