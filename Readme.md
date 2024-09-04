Original IronMask repository: https://github.com/CryptoExperts/IronMask (contains compilation information)

# IronMask+: Verification of Combined Random Fault Security

To reproduce the results from the paper, you need to run three commands:

* sage src/test_correction.py -p CRPC -f 'gadget_filename' -s 'fault_type (1 set, 0 reset)' -k 'nb_faults': this command produces the faulty scenarios which cannot be corrected, necessary to compute the value of mu
* ./ironmask gadget_filename -k 'nb_faults' -s 'fault_type' -c 'nb_coeffs' -t 1: this command runs the first step of the verification for the combined property. Once this is done executing, you can run the following command for any leakage and fault probabilities:
* ./ironmask gadget_filename -k 'nb_faults' -s 'fault_type' -c 'nb_coeffs' -t 1 -l 0,001 -f 0,001 for example for a leakage and fault probabilities of 0,001 each

# License

[GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html)
