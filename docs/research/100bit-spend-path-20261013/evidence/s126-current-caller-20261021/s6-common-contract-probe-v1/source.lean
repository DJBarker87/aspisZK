import S6SourcePaymentCommonContentsV1
import S6SourcePaymentCommonEncodeTotalV1
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentContents
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.payment_relation
set_option pp.fullNames true in
#check common_contents
set_option pp.fullNames true in
#check encode_common
set_option pp.fullNames true in
#check @PaymentEncodeTotal.common_write_total
end AspisS6SourceCodec.PaymentContents
