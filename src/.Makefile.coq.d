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
