Record_Geo_Vec.vo Record_Geo_Vec.glob Record_Geo_Vec.v.beautified Record_Geo_Vec.required_vo: Record_Geo_Vec.v 
Record_Geo_Vec.vos Record_Geo_Vec.vok Record_Geo_Vec.required_vos: Record_Geo_Vec.v 
Record_Geo_Point.vo Record_Geo_Point.glob Record_Geo_Point.v.beautified Record_Geo_Point.required_vo: Record_Geo_Point.v Record_Geo_Vec.vo
Record_Geo_Point.vos Record_Geo_Point.vok Record_Geo_Point.required_vos: Record_Geo_Point.v Record_Geo_Vec.vos
Geo_Predicates.vo Geo_Predicates.glob Geo_Predicates.v.beautified Geo_Predicates.required_vo: Geo_Predicates.v Record_Geo_Point.vo Record_Geo_Vec.vo
Geo_Predicates.vos Geo_Predicates.vok Geo_Predicates.required_vos: Geo_Predicates.v Record_Geo_Point.vos Record_Geo_Vec.vos
Point_Order.vo Point_Order.glob Point_Order.v.beautified Point_Order.required_vo: Point_Order.v Record_Geo_Point.vo Record_Geo_Vec.vo
Point_Order.vos Point_Order.vok Point_Order.required_vos: Point_Order.v Record_Geo_Point.vos Record_Geo_Vec.vos
Point_Array_Specs.vo Point_Array_Specs.glob Point_Array_Specs.v.beautified Point_Array_Specs.required_vo: Point_Array_Specs.v ../listlib/Base/Positional.vo Record_Geo_Point.vo Point_Order.vo
Point_Array_Specs.vos Point_Array_Specs.vok Point_Array_Specs.required_vos: Point_Array_Specs.v ../listlib/Base/Positional.vos Record_Geo_Point.vos Point_Order.vos
Sort.vo Sort.glob Sort.v.beautified Sort.required_vo: Sort.v Record_Geo_Point.vo Point_Order.vo Point_Array_Specs.vo
Sort.vos Sort.vok Sort.required_vos: Sort.v Record_Geo_Point.vos Point_Order.vos Point_Array_Specs.vos
Hull_Equiv.vo Hull_Equiv.glob Hull_Equiv.v.beautified Hull_Equiv.required_vo: Hull_Equiv.v Record_Geo_Point.vo Record_Geo_Vec.vo
Hull_Equiv.vos Hull_Equiv.vok Hull_Equiv.required_vos: Hull_Equiv.v Record_Geo_Point.vos Record_Geo_Vec.vos
Graham_Scan.vo Graham_Scan.glob Graham_Scan.v.beautified Graham_Scan.required_vo: Graham_Scan.v Record_Geo_Vec.vo Record_Geo_Point.vo
Graham_Scan.vos Graham_Scan.vok Graham_Scan.required_vos: Graham_Scan.v Record_Geo_Vec.vos Record_Geo_Point.vos
Graham_Scan_M.vo Graham_Scan_M.glob Graham_Scan_M.v.beautified Graham_Scan_M.required_vo: Graham_Scan_M.v Record_Geo_Vec.vo Record_Geo_Point.vo Graham_Scan.vo Hull_Equiv.vo ../sets/SetsClass.vo ../MonadLib/Monad.vo ../MonadLib/StateRelMonad/StateRelBasic.vo ../MonadLib/StateRelMonad/StateRelMonad.vo ../MonadLib/StateRelMonad/StateRelHoare.vo ../MonadLib/StateRelMonad/FixpointLib.vo
Graham_Scan_M.vos Graham_Scan_M.vok Graham_Scan_M.required_vos: Graham_Scan_M.v Record_Geo_Vec.vos Record_Geo_Point.vos Graham_Scan.vos Hull_Equiv.vos ../sets/SetsClass.vos ../MonadLib/Monad.vos ../MonadLib/StateRelMonad/StateRelBasic.vos ../MonadLib/StateRelMonad/StateRelMonad.vos ../MonadLib/StateRelMonad/StateRelHoare.vos ../MonadLib/StateRelMonad/FixpointLib.vos
Reversal.vo Reversal.glob Reversal.v.beautified Reversal.required_vo: Reversal.v Record_Geo_Point.vo Record_Geo_Vec.vo Graham_Scan.vo Hull_Equiv.vo Graham_Scan_M.vo
Reversal.vos Reversal.vok Reversal.required_vos: Reversal.v Record_Geo_Point.vos Record_Geo_Vec.vos Graham_Scan.vos Hull_Equiv.vos Graham_Scan_M.vos
ConvexHull.vo ConvexHull.glob ConvexHull.v.beautified ConvexHull.required_vo: ConvexHull.v Record_Geo_Vec.vo Record_Geo_Point.vo Point_Order.vo Point_Array_Specs.vo Sort.vo Hull_Equiv.vo Graham_Scan.vo Graham_Scan_M.vo Reversal.vo
ConvexHull.vos ConvexHull.vok ConvexHull.required_vos: ConvexHull.v Record_Geo_Vec.vos Record_Geo_Point.vos Point_Order.vos Point_Array_Specs.vos Sort.vos Hull_Equiv.vos Graham_Scan.vos Graham_Scan_M.vos Reversal.vos
