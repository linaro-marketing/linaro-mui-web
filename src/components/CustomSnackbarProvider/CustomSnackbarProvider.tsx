// Generated with util/create-component.js
import React from "react";
import { CustomSnackbarProviderProps } from "./CustomSnackbarProvider.types";
import Button from "@mui/material/Button";
import { SnackbarProvider } from "notistack";

/**
 * Custom SnackbarProvider component
 * @param {props} props
 * @component
 */
const CustomSnackbarProvider: React.FC<CustomSnackbarProviderProps> = ({
  children,
  notistackRef,
  dismissText,
  ...rest
}) => {
  const dismissSnackbar = (key: any) => () => {
    if (notistackRef) {
      notistackRef.current.closeSnackbar(key);
    }
  };
  return (
    <SnackbarProvider
      ref={notistackRef}
      maxSnack={3}
      autoHideDuration={2000}
      action={(key) => (
        <Button
          sx={{
            color: "background.default",
          }}
          onClick={dismissSnackbar(key)}
        >
          {dismissText}
        </Button>
      )}
      {...rest}
    >
      {children}
    </SnackbarProvider>
  );
};
export default CustomSnackbarProvider;
