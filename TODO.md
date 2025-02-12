# TODO

1. Jarvis_March 凸包实现在末尾加入初始点？
   当前实现未加入，导致对凸包递归时没有考虑最后一条边

2. Jarvis_March 补充凸包证明 (theories/Jarvis_March.v:190)
   思路：由 sort 导出 g_ccw_list & consec_ccw，
        证明 jarvis_march_aux 凸包扩张的归纳性质

3. Graham_Andrew 算法实现仍使用 ccw_dec，共线处理有误

4. 后续证明
