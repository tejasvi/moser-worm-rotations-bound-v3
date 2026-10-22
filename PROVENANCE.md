# Provenance of the released files

For each file that comes from the runs, the table gives the SHA-256 hash of the version that ran (for the checker
files, the versions that produced the check logs; for the search programs, the versions recorded in the part
headers) and the hash of the released file. "AST identical up to docstrings" means that both files parse to the
same Python syntax tree once docstrings are removed; comments are not part of the tree. Files marked "new" were
written for the paper after the runs.

| file | SHA-256 of the version that ran | SHA-256 of this file | changes |
|---|---|---|---|
| checker/wcheck.py | 520e291eac2712c53ba3c8f8de7ad45b53c7121b37e9bc0b30bedf39899b9d2a | fb0d9a6992740243c56fc8cde9503f5708c76b62822d8f61275b37bb6e38a415 | docstrings and one comment edited (no internal note names; description of W corrected; model() marked unused); AST identical up to docstrings |
| checker/wcheck_v2.py | 9374fec55c2ebdf50193ade9c31c3e2608e6ebe77f4ec6d38a36845ae95d7e8d | 27914a130c382ab903475b51a0a04d0d3f4ffca93b7f22841f64f5f3b980d615 | docstrings and one comment edited (no internal note names; description of W corrected; model() marked unused); AST identical up to docstrings |
| checker/wcheck_presence.py | 645b0e2656b94f056bd15c941af8823023103577596819e4567954ec8fdddfac | 645b0e2656b94f056bd15c941af8823023103577596819e4567954ec8fdddfac | identical |
| checker/wcheck_presence_v2.py | 9e7cbbd33799cd943f3042474ea4f449599bcbc18652be447c93c30020c9034e | 9e7cbbd33799cd943f3042474ea4f449599bcbc18652be447c93c30020c9034e | identical |
| checker/wcheck_selftest.py | 4cf1a9d4a443909e28aa52f6f20ca91612c611ddc9c565eea08ac272740ee206 | 4cf1a9d4a443909e28aa52f6f20ca91612c611ddc9c565eea08ac272740ee206 | identical |
| checker/negtest_leaf.py | - | 40a5a41603aebdc139795645be540e95d2d35f3cced7dbfa8441ccab4f7d3163 | new |
| checker/check_headers.py | - | 73dfe6f20c3dfc890f4c084dd9e7db3e42c01b6985cee8c1907504d6f6774270 | new |
| checker/negtest_winding.py | - | 4d14a7a658cf196dd9f56a0dbc6468d5adbe8c1223899cd9b259ea301bba2e27 | new |
| checker/testcert/part31010.json | 4223c8b4fa87fbbed18a48e513db5c0a4881e607d576a499974b47552cfb42b2 | 4223c8b4fa87fbbed18a48e513db5c0a4881e607d576a499974b47552cfb42b2 | identical |
| checker/testcert/part31010.leaves.jsonl.gz | 7b7a1bbf12b08bf171f48df734554ae037157c0e847dc03671d4186cf2812047 | 7b7a1bbf12b08bf171f48df734554ae037157c0e847dc03671d4186cf2812047 | identical |
| checker/testcert/part31010.npy | 70e874b75c17dc5635ac2c9864e80790b2b7e99f275b254ac0d912cfd586452f | 70e874b75c17dc5635ac2c9864e80790b2b7e99f275b254ac0d912cfd586452f | identical |
| checker/testcert/part49490.json | 8030afd0a9d5e831a02c5f1a4a70d2c4668b67398fc8778e8053b1f5f7a7cd67 | 8030afd0a9d5e831a02c5f1a4a70d2c4668b67398fc8778e8053b1f5f7a7cd67 | identical |
| checker/testcert/part49490.leaves.jsonl.gz | 0d2b351b244d31e3824dc7a3d1062ad8ab22be920ca926127c35715ac05b26c8 | 0d2b351b244d31e3824dc7a3d1062ad8ab22be920ca926127c35715ac05b26c8 | identical |
| checker/testcert/part49490.npy | f204a17322e91ede8430fc082bcaf5810188600a9f3cdedb74916f3c70d7a125 | f204a17322e91ede8430fc082bcaf5810188600a9f3cdedb74916f3c70d7a125 | identical |
| checker/testcert/part5613.json | 5ea561f36bb331d824550ea63f362a0cd632cf7d78ea80f6b70ca56b4911be6b | 5ea561f36bb331d824550ea63f362a0cd632cf7d78ea80f6b70ca56b4911be6b | identical |
| checker/testcert/part5613.leaves.jsonl.gz | 93a97794e0945afebfdebecfa20446898438bda946c9cb3117ebb696ca739044 | 93a97794e0945afebfdebecfa20446898438bda946c9cb3117ebb696ca739044 | identical |
| checker/testcert/part5613.npy | a30efe3553f1f03e42aa0828c345ceb305cae4b39ba350b7e1e6d7d1311365cc | a30efe3553f1f03e42aa0828c345ceb305cae4b39ba350b7e1e6d7d1311365cc | identical |
| checker/testcert/part62289.json | bc7649f1635e1fe0c23bb4885355e2a6cf684dc231648fc35b9a1a747f3a1c82 | bc7649f1635e1fe0c23bb4885355e2a6cf684dc231648fc35b9a1a747f3a1c82 | identical |
| checker/testcert/part62289.leaves.jsonl.gz | 8714c20a4004829d195c04567dade6e36b84a03e1605d5b37e190537cd729958 | 8714c20a4004829d195c04567dade6e36b84a03e1605d5b37e190537cd729958 | identical |
| checker/testcert/part62289.npy | 72541dae69908589d38a01a13d51140b75723bb1a41e1a855fbbb0ec46460bce | 72541dae69908589d38a01a13d51140b75723bb1a41e1a855fbbb0ec46460bce | identical |
| data/opt_point.json | - | a9364694ac8086d009b08e9cdd0c81d9339104841a8948712cd315d7747089ef | new |
| checker/logs/check_lines.jsonl.gz | - | 62c5ca902b2f4dcadffff7b6a5b5ec3d6f744a2766ffffc69f8ef022ff6e92c6 | 16638 lines (deduplicated, sorted by part and leaf range) |
| checker/logs/SUMMARY.json | f8626ad4e90d857f461193870e96426a392bbfb95aabb83e07fa0f183b15aedd | f8626ad4e90d857f461193870e96426a392bbfb95aabb83e07fa0f183b15aedd | identical |
| search/run5b_f80e8996.py | f80e8996a81d0ca684b977c08e81b0773e5936d03bd562dbe36e62338cb4765c | f80e8996a81d0ca684b977c08e81b0773e5936d03bd562dbe36e62338cb4765c | identical |
| search/wsearch_b837e347.py | b837e3478c973c5a2bb6d656852296ecc4fb66e4ba079d8ea54b2925dada22e7 | 6817241c7dbaae148b314e33f2e60276c63246aa9e0b610b96892214ac6035c3 | 3 sys.path line(s) relative to the file; docstring edited (internal paths or note names replaced by neutral text) |
| search/wbnb_b4042d07.py | b4042d0741a67da1f82119725a87617e95d6155d883bbf5729871032803aeff7 | e42269195e41b361fa3addcdb1042917429a19c9cd6af94bad80c85d5d199a57 | 1 sys.path line(s) relative to the file |
| search/wchord_eec210b9.py | eec210b95a8dd1ae70b898882f37f912ffbbccdde6bb90f2e396a66676d7011a | fa5f179bc1db07ab45f18a174f21ed510849677b74571bef1ca02b6ad0a9ac69 | 2 sys.path line(s) relative to the file |
| search/lbsearch_94f78046.py | 94f78046e11dc75fcf7c300b771552f98bbd7a2daf8f912fc3345bbc383253aa | 7fe586a43a9d7916565f9b7fe24c6bacf01c78ac8b152ca211cf97dfe88ddb32 | docstring edited (internal paths or note names replaced by neutral text) |
| search/wtask_5acd5ac0.py | 5acd5ac00cb5eb762228f137b8434eab689eeef410288c6920ea36fc6206f270 | 5acd5ac00cb5eb762228f137b8434eab689eeef410288c6920ea36fc6206f270 | identical |
| search/wtask_ab6507da.py | ab6507daa644b2b3c7b1fd350bf3e5d82adc354ae9b218526d155911847589f5 | ab6507daa644b2b3c7b1fd350bf3e5d82adc354ae9b218526d155911847589f5 | identical |
| search/worm_ff8e285a.py | ff8e285aec65e7a635dbf8fdde5a7649694e23065aa628b9cfbf12ab52fb9a68 | ff8e285aec65e7a635dbf8fdde5a7649694e23065aa628b9cfbf12ab52fb9a68 | identical |
| search/fammin_964be377.py | 964be3777fe7eea69a34f217895564dffbb30e0a820c5f152f5c4460b3168a91 | 964be3777fe7eea69a34f217895564dffbb30e0a820c5f152f5c4460b3168a91 | identical |
| search/wfam_17da1a7b.py | 17da1a7b596fafc06ffa36c050a50e7d991dffd7f9c32807b207e99691597352 | 17da1a7b596fafc06ffa36c050a50e7d991dffd7f9c32807b207e99691597352 | identical |
| search/assemble_195ccd91.py | 195ccd91cee3456b1994e029e2790ed791e77158095cfbe0531d27e80e92866c | 195ccd91cee3456b1994e029e2790ed791e77158095cfbe0531d27e80e92866c | identical |
| search/wfam_261fc37d.py | 261fc37dc158ee70d8de04f8ec417fdb859dc4c50f1513fcf4526a157fadca53 | 289c4818b4d8705291c92a2b638631e3a42eac4eb107fdeb660e9cadd4527a78 | one comment edited (no names) |
| search/fitscale_487e12fd.py | 487e12fdf911fbd19be640d014fbba895c99cc179138763f603d8f7a19dc9f48 | 487e12fdf911fbd19be640d014fbba895c99cc179138763f603d8f7a19dc9f48 | identical |

## Lean files (`lean/`)

`lean/` holds the 7,046 files of the Lean development that was built and checked, unchanged; the data of the formal proof (`lean/data/`) comes from the archives of the supplement record. Third-party files: see `lean/PROVENANCE.md`.
