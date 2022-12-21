import React from "react";
import { render } from "@testing-library/react";
import CustomSnackbarProvider from "./CustomSnackbarProvider";
import { CustomSnackbarProviderProps } from "./CustomSnackbarProvider.types";
describe("CustomSnackbarProvider Test", () => {
  test("renders the CustomSnackbarProvider component", () => {
    render(
      <CustomSnackbarProvider dismissText="dismiss">
        <></>
      </CustomSnackbarProvider>
    );
  });
});
